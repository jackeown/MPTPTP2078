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
% DateTime   : Thu Dec  3 12:54:11 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 240 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  250 ( 865 expanded)
%              Number of equality atoms :   62 ( 119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1032,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f780,f791,f1027])).

fof(f1027,plain,(
    ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f1026])).

fof(f1026,plain,
    ( $false
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f1010,f40])).

fof(f40,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f1010,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_15 ),
    inference(superposition,[],[f497,f982])).

fof(f982,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f981,f779])).

fof(f779,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f777])).

fof(f777,plain,
    ( spl3_15
  <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f981,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f980,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f980,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f979,f779])).

fof(f979,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f978,f39])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f978,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f977,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f977,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ v1_relat_1(sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f967,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f967,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ v2_funct_1(sK2) ),
    inference(superposition,[],[f195,f651])).

fof(f651,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f631,f72])).

fof(f72,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f71,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f54,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f41,f42])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f631,plain,(
    k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f266,f85])).

fof(f85,plain,(
    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f56,f37])).

fof(f37,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f266,plain,(
    ! [X0,X1] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(subsumption_resolution,[],[f265,f35])).

fof(f265,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f264,f36])).

fof(f264,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f228,f39])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f227,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f62,f61])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f57,f59,f59])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f195,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k10_relat_1(X3,k9_relat_1(X3,X4)))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k10_relat_1(X3,k9_relat_1(X3,X4)) = X4
      | ~ v2_funct_1(X3) ) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f497,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f470,f61])).

fof(f470,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f42,f150])).

fof(f150,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f45,f45])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f791,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | spl3_14 ),
    inference(subsumption_resolution,[],[f789,f35])).

fof(f789,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(subsumption_resolution,[],[f788,f36])).

fof(f788,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(subsumption_resolution,[],[f787,f39])).

fof(f787,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(resolution,[],[f775,f49])).

fof(f775,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl3_14
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f780,plain,
    ( ~ spl3_14
    | spl3_15 ),
    inference(avatar_split_clause,[],[f770,f777,f773])).

fof(f770,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f751,f52])).

fof(f751,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(trivial_inequality_removal,[],[f740])).

fof(f740,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f55,f717])).

fof(f717,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f708,f35])).

fof(f708,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f170,f38])).

fof(f38,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f170,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k1_relat_1(X6))
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = k4_xboole_0(X5,k10_relat_1(X6,k9_relat_1(X6,X5))) ) ),
    inference(resolution,[],[f47,f56])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (27285)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (27293)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (27301)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.52/0.57  % (27284)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % (27292)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.58  % (27282)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.67/0.58  % (27300)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.67/0.59  % (27281)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.67/0.60  % (27278)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.67/0.60  % (27280)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.67/0.60  % (27299)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.67/0.60  % (27303)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.67/0.60  % (27306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.67/0.60  % (27295)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.67/0.61  % (27294)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.67/0.61  % (27307)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.67/0.61  % (27289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.67/0.61  % (27304)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.67/0.61  % (27287)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.67/0.61  % (27283)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.67/0.61  % (27297)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.67/0.61  % (27298)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.67/0.62  % (27288)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.67/0.62  % (27286)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.67/0.62  % (27279)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.67/0.62  % (27290)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.67/0.62  % (27302)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.67/0.62  % (27296)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.67/0.62  % (27291)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.67/0.63  % (27305)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.17/0.65  % (27284)Refutation found. Thanks to Tanya!
% 2.17/0.65  % SZS status Theorem for theBenchmark
% 2.17/0.65  % SZS output start Proof for theBenchmark
% 2.17/0.65  fof(f1032,plain,(
% 2.17/0.65    $false),
% 2.17/0.65    inference(avatar_sat_refutation,[],[f780,f791,f1027])).
% 2.17/0.65  fof(f1027,plain,(
% 2.17/0.65    ~spl3_15),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f1026])).
% 2.17/0.65  fof(f1026,plain,(
% 2.17/0.65    $false | ~spl3_15),
% 2.17/0.65    inference(subsumption_resolution,[],[f1010,f40])).
% 2.17/0.65  fof(f40,plain,(
% 2.17/0.65    ~r1_tarski(sK0,sK1)),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f30,plain,(
% 2.17/0.65    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.17/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f29])).
% 2.17/0.65  fof(f29,plain,(
% 2.17/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.17/0.65    introduced(choice_axiom,[])).
% 2.17/0.65  fof(f18,plain,(
% 2.17/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.17/0.65    inference(flattening,[],[f17])).
% 2.17/0.65  fof(f17,plain,(
% 2.17/0.65    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.17/0.65    inference(ennf_transformation,[],[f16])).
% 2.17/0.65  fof(f16,negated_conjecture,(
% 2.17/0.65    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.17/0.65    inference(negated_conjecture,[],[f15])).
% 2.17/0.65  fof(f15,conjecture,(
% 2.17/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 2.17/0.65  fof(f1010,plain,(
% 2.17/0.65    r1_tarski(sK0,sK1) | ~spl3_15),
% 2.17/0.65    inference(superposition,[],[f497,f982])).
% 2.17/0.65  fof(f982,plain,(
% 2.17/0.65    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_15),
% 2.17/0.65    inference(forward_demodulation,[],[f981,f779])).
% 2.17/0.65  fof(f779,plain,(
% 2.17/0.65    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_15),
% 2.17/0.65    inference(avatar_component_clause,[],[f777])).
% 2.17/0.65  fof(f777,plain,(
% 2.17/0.65    spl3_15 <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.17/0.65  fof(f981,plain,(
% 2.17/0.65    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_15),
% 2.17/0.65    inference(subsumption_resolution,[],[f980,f42])).
% 2.17/0.65  fof(f42,plain,(
% 2.17/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f5])).
% 2.17/0.65  fof(f5,axiom,(
% 2.17/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.17/0.65  fof(f980,plain,(
% 2.17/0.65    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_15),
% 2.17/0.65    inference(forward_demodulation,[],[f979,f779])).
% 2.17/0.65  fof(f979,plain,(
% 2.17/0.65    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 2.17/0.65    inference(subsumption_resolution,[],[f978,f39])).
% 2.17/0.65  fof(f39,plain,(
% 2.17/0.65    v2_funct_1(sK2)),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f978,plain,(
% 2.17/0.65    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f977,f35])).
% 2.17/0.65  fof(f35,plain,(
% 2.17/0.65    v1_relat_1(sK2)),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f977,plain,(
% 2.17/0.65    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~v1_relat_1(sK2) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 2.17/0.65    inference(subsumption_resolution,[],[f967,f36])).
% 2.17/0.65  fof(f36,plain,(
% 2.17/0.65    v1_funct_1(sK2)),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f967,plain,(
% 2.17/0.65    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~v2_funct_1(sK2)),
% 2.17/0.65    inference(superposition,[],[f195,f651])).
% 2.17/0.65  fof(f651,plain,(
% 2.17/0.65    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.17/0.65    inference(forward_demodulation,[],[f631,f72])).
% 2.17/0.65  fof(f72,plain,(
% 2.17/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.17/0.65    inference(resolution,[],[f71,f53])).
% 2.17/0.65  fof(f53,plain,(
% 2.17/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.17/0.65    inference(cnf_transformation,[],[f33])).
% 2.17/0.65  fof(f33,plain,(
% 2.17/0.65    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.17/0.65    inference(nnf_transformation,[],[f8])).
% 2.17/0.65  fof(f8,axiom,(
% 2.17/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.17/0.65  fof(f71,plain,(
% 2.17/0.65    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 2.17/0.65    inference(resolution,[],[f69,f48])).
% 2.17/0.65  fof(f48,plain,(
% 2.17/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f22])).
% 2.17/0.65  fof(f22,plain,(
% 2.17/0.65    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.17/0.65    inference(ennf_transformation,[],[f1])).
% 2.17/0.65  fof(f1,axiom,(
% 2.17/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.17/0.65  fof(f69,plain,(
% 2.17/0.65    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f68])).
% 2.17/0.65  fof(f68,plain,(
% 2.17/0.65    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 2.17/0.65    inference(superposition,[],[f54,f66])).
% 2.17/0.65  fof(f66,plain,(
% 2.17/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.17/0.65    inference(resolution,[],[f41,f42])).
% 2.17/0.65  fof(f41,plain,(
% 2.17/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.17/0.65    inference(cnf_transformation,[],[f19])).
% 2.17/0.65  fof(f19,plain,(
% 2.17/0.65    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.17/0.65    inference(ennf_transformation,[],[f6])).
% 2.17/0.65  fof(f6,axiom,(
% 2.17/0.65    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.17/0.65  fof(f54,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f33])).
% 2.17/0.65  fof(f631,plain,(
% 2.17/0.65    k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.17/0.65    inference(superposition,[],[f266,f85])).
% 2.17/0.65  fof(f85,plain,(
% 2.17/0.65    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.17/0.65    inference(resolution,[],[f56,f37])).
% 2.17/0.65  fof(f37,plain,(
% 2.17/0.65    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f56,plain,(
% 2.17/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.17/0.65    inference(cnf_transformation,[],[f34])).
% 2.17/0.65  fof(f34,plain,(
% 2.17/0.65    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.17/0.65    inference(nnf_transformation,[],[f3])).
% 2.17/0.65  fof(f3,axiom,(
% 2.17/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.17/0.65  fof(f266,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.17/0.65    inference(subsumption_resolution,[],[f265,f35])).
% 2.17/0.65  fof(f265,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(sK2)) )),
% 2.17/0.65    inference(subsumption_resolution,[],[f264,f36])).
% 2.17/0.65  fof(f264,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.17/0.65    inference(resolution,[],[f228,f39])).
% 2.17/0.65  fof(f228,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.17/0.65    inference(forward_demodulation,[],[f227,f61])).
% 2.17/0.65  fof(f61,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.17/0.65    inference(definition_unfolding,[],[f46,f59])).
% 2.17/0.65  fof(f59,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.17/0.65    inference(definition_unfolding,[],[f44,f45])).
% 2.17/0.65  fof(f45,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f10])).
% 2.17/0.65  fof(f10,axiom,(
% 2.17/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 2.17/0.65  fof(f44,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.17/0.65    inference(cnf_transformation,[],[f11])).
% 2.17/0.65  fof(f11,axiom,(
% 2.17/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.17/0.65  fof(f46,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f7])).
% 2.17/0.65  fof(f7,axiom,(
% 2.17/0.65    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.17/0.65  fof(f227,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.17/0.65    inference(forward_demodulation,[],[f62,f61])).
% 2.17/0.65  fof(f62,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.17/0.65    inference(definition_unfolding,[],[f57,f59,f59])).
% 2.17/0.65  fof(f57,plain,(
% 2.17/0.65    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f26])).
% 2.17/0.65  fof(f26,plain,(
% 2.17/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.17/0.65    inference(flattening,[],[f25])).
% 2.17/0.65  fof(f25,plain,(
% 2.17/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.17/0.65    inference(ennf_transformation,[],[f12])).
% 2.17/0.65  fof(f12,axiom,(
% 2.17/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 2.17/0.65  fof(f195,plain,(
% 2.17/0.65    ( ! [X4,X3] : (~r1_tarski(X4,k10_relat_1(X3,k9_relat_1(X3,X4))) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k10_relat_1(X3,k9_relat_1(X3,X4)) = X4 | ~v2_funct_1(X3)) )),
% 2.17/0.65    inference(resolution,[],[f49,f52])).
% 2.17/0.65  fof(f52,plain,(
% 2.17/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f32])).
% 2.17/0.65  fof(f32,plain,(
% 2.17/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.65    inference(flattening,[],[f31])).
% 2.17/0.65  fof(f31,plain,(
% 2.17/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.65    inference(nnf_transformation,[],[f2])).
% 2.17/0.65  fof(f2,axiom,(
% 2.17/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.17/0.65  fof(f49,plain,(
% 2.17/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f24])).
% 2.17/0.65  fof(f24,plain,(
% 2.17/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.17/0.65    inference(flattening,[],[f23])).
% 2.17/0.65  fof(f23,plain,(
% 2.17/0.65    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.17/0.65    inference(ennf_transformation,[],[f14])).
% 2.17/0.65  fof(f14,axiom,(
% 2.17/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 2.17/0.65  fof(f497,plain,(
% 2.17/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 2.17/0.65    inference(forward_demodulation,[],[f470,f61])).
% 2.17/0.65  fof(f470,plain,(
% 2.17/0.65    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 2.17/0.65    inference(superposition,[],[f42,f150])).
% 2.17/0.65  fof(f150,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 2.17/0.65    inference(superposition,[],[f61,f60])).
% 2.17/0.65  fof(f60,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.17/0.65    inference(definition_unfolding,[],[f43,f45,f45])).
% 2.17/0.65  fof(f43,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f9])).
% 2.17/0.65  fof(f9,axiom,(
% 2.17/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.17/0.65  fof(f791,plain,(
% 2.17/0.65    spl3_14),
% 2.17/0.65    inference(avatar_contradiction_clause,[],[f790])).
% 2.17/0.65  fof(f790,plain,(
% 2.17/0.65    $false | spl3_14),
% 2.17/0.65    inference(subsumption_resolution,[],[f789,f35])).
% 2.17/0.65  fof(f789,plain,(
% 2.17/0.65    ~v1_relat_1(sK2) | spl3_14),
% 2.17/0.65    inference(subsumption_resolution,[],[f788,f36])).
% 2.17/0.65  fof(f788,plain,(
% 2.17/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_14),
% 2.17/0.65    inference(subsumption_resolution,[],[f787,f39])).
% 2.17/0.65  fof(f787,plain,(
% 2.17/0.65    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_14),
% 2.17/0.65    inference(resolution,[],[f775,f49])).
% 2.17/0.65  fof(f775,plain,(
% 2.17/0.65    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) | spl3_14),
% 2.17/0.65    inference(avatar_component_clause,[],[f773])).
% 2.17/0.65  fof(f773,plain,(
% 2.17/0.65    spl3_14 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.17/0.65  fof(f780,plain,(
% 2.17/0.65    ~spl3_14 | spl3_15),
% 2.17/0.65    inference(avatar_split_clause,[],[f770,f777,f773])).
% 2.17/0.65  fof(f770,plain,(
% 2.17/0.65    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 2.17/0.65    inference(resolution,[],[f751,f52])).
% 2.17/0.65  fof(f751,plain,(
% 2.17/0.65    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.17/0.65    inference(trivial_inequality_removal,[],[f740])).
% 2.17/0.65  fof(f740,plain,(
% 2.17/0.65    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.17/0.65    inference(superposition,[],[f55,f717])).
% 2.17/0.65  fof(f717,plain,(
% 2.17/0.65    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.17/0.65    inference(subsumption_resolution,[],[f708,f35])).
% 2.17/0.65  fof(f708,plain,(
% 2.17/0.65    ~v1_relat_1(sK2) | k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.17/0.65    inference(resolution,[],[f170,f38])).
% 2.17/0.65  fof(f38,plain,(
% 2.17/0.65    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.17/0.65    inference(cnf_transformation,[],[f30])).
% 2.17/0.65  fof(f170,plain,(
% 2.17/0.65    ( ! [X6,X5] : (~r1_tarski(X5,k1_relat_1(X6)) | ~v1_relat_1(X6) | k1_xboole_0 = k4_xboole_0(X5,k10_relat_1(X6,k9_relat_1(X6,X5)))) )),
% 2.17/0.65    inference(resolution,[],[f47,f56])).
% 2.17/0.65  fof(f47,plain,(
% 2.17/0.65    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f21])).
% 2.17/0.65  fof(f21,plain,(
% 2.17/0.65    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.17/0.65    inference(flattening,[],[f20])).
% 2.17/0.65  fof(f20,plain,(
% 2.17/0.65    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.17/0.65    inference(ennf_transformation,[],[f13])).
% 2.17/0.65  fof(f13,axiom,(
% 2.17/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.17/0.65  fof(f55,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f34])).
% 2.17/0.65  % SZS output end Proof for theBenchmark
% 2.17/0.65  % (27284)------------------------------
% 2.17/0.65  % (27284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (27284)Termination reason: Refutation
% 2.17/0.65  
% 2.17/0.65  % (27284)Memory used [KB]: 11257
% 2.17/0.65  % (27284)Time elapsed: 0.200 s
% 2.17/0.65  % (27284)------------------------------
% 2.17/0.65  % (27284)------------------------------
% 2.17/0.65  % (27277)Success in time 0.287 s
%------------------------------------------------------------------------------
