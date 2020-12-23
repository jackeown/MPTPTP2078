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
% DateTime   : Thu Dec  3 12:55:58 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 795 expanded)
%              Number of leaves         :   20 ( 210 expanded)
%              Depth                    :   21
%              Number of atoms          :  272 (1836 expanded)
%              Number of equality atoms :   66 ( 635 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f762,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f379,f386,f752])).

fof(f752,plain,
    ( ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f751])).

fof(f751,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f750,f90])).

fof(f90,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[],[f44,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
    inference(resolution,[],[f42,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f44,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f750,plain,
    ( k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f496,f749])).

fof(f749,plain,
    ( k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f745,f373])).

fof(f373,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl4_9
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f745,plain,
    ( k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,sK0)) ),
    inference(resolution,[],[f740,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f740,plain,(
    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    inference(superposition,[],[f719,f160])).

fof(f160,plain,(
    ! [X1] : k2_wellord1(sK2,X1) = k2_wellord1(k2_wellord1(sK2,X1),k3_relat_1(sK2)) ),
    inference(superposition,[],[f72,f158])).

fof(f158,plain,(
    sK2 = k2_wellord1(sK2,k3_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f157,f147])).

fof(f147,plain,(
    sK2 = k8_relat_1(k3_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f143,plain,
    ( sK2 = k8_relat_1(k3_relat_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f135,f51])).

fof(f135,plain,(
    r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2)) ),
    inference(resolution,[],[f110,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,k3_relat_1(sK2)) ) ),
    inference(superposition,[],[f69,f74])).

fof(f74,plain,(
    k3_relat_1(sK2) = k3_tarski(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f42,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f157,plain,(
    k8_relat_1(k3_relat_1(sK2),sK2) = k2_wellord1(sK2,k3_relat_1(sK2)) ),
    inference(superposition,[],[f73,f116])).

fof(f116,plain,(
    sK2 = k7_relat_1(sK2,k3_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f112,plain,
    ( sK2 = k7_relat_1(sK2,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f111,plain,(
    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) ),
    inference(superposition,[],[f68,f74])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f73,plain,(
    ! [X2] : k2_wellord1(sK2,X2) = k8_relat_1(X2,k7_relat_1(sK2,X2)) ),
    inference(resolution,[],[f42,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f719,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k2_wellord1(k2_wellord1(sK2,sK0),X0)),sK1) ),
    inference(resolution,[],[f555,f71])).

fof(f555,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(k2_wellord1(k2_wellord1(sK2,sK0),X1)))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f325,f217])).

fof(f217,plain,(
    ! [X0,X1] : r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X0) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X0) ) ),
    inference(resolution,[],[f205,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2) ) ),
    inference(subsumption_resolution,[],[f203,f42])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f165,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k2_wellord1(sK2,X1))
      | r2_hidden(sK3(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2) ) ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_relat_1(k2_wellord1(k2_wellord1(sK2,X4),X3)))
      | r2_hidden(X5,X4)
      | ~ v1_relat_1(k2_wellord1(sK2,X3)) ) ),
    inference(superposition,[],[f62,f72])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f325,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X2),X3)),sK0)
      | r1_tarski(X4,sK1)
      | ~ r1_tarski(X4,k2_relat_1(k2_wellord1(k2_wellord1(sK2,X2),X3))) ) ),
    inference(superposition,[],[f99,f258])).

fof(f258,plain,(
    ! [X0,X1] : k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k2_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)))) ),
    inference(subsumption_resolution,[],[f256,f42])).

fof(f256,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k2_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1))))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f140,f49])).

fof(f140,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(k2_wellord1(sK2,X7))
      | k3_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)),k2_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)))) ) ),
    inference(resolution,[],[f93,f67])).

fof(f93,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k2_wellord1(k2_wellord1(sK2,X7),X6))
      | ~ v1_relat_1(k2_wellord1(sK2,X6)) ) ),
    inference(superposition,[],[f49,f72])).

fof(f99,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X3,X3,X3,X4)),sK0)
      | r1_tarski(X2,sK1)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f88,f69])).

fof(f88,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | r1_tarski(X3,sK1)
      | ~ r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f75,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f75,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f43,f64])).

fof(f43,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f496,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_10 ),
    inference(superposition,[],[f198,f378])).

fof(f378,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl4_10
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f198,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k8_relat_1(X1,k7_relat_1(k2_wellord1(sK2,X0),X1)) ),
    inference(superposition,[],[f197,f158])).

fof(f197,plain,(
    ! [X2,X0,X1] : k2_wellord1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2)) ),
    inference(subsumption_resolution,[],[f195,f42])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(k2_wellord1(sK2,X4))
      | k2_wellord1(k2_wellord1(k2_wellord1(sK2,X5),X4),X6) = k8_relat_1(X6,k7_relat_1(k2_wellord1(k2_wellord1(sK2,X5),X4),X6)) ) ),
    inference(resolution,[],[f93,f50])).

fof(f386,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f384,f42])).

fof(f384,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(resolution,[],[f374,f49])).

fof(f374,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f372])).

fof(f379,plain,
    ( ~ spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f369,f376,f372])).

fof(f369,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0)) ),
    inference(resolution,[],[f355,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),sK0)
      | k7_relat_1(X1,sK1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f75,f52])).

fof(f355,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k2_wellord1(sK2,X1)),X1) ),
    inference(resolution,[],[f350,f231])).

fof(f231,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k3_relat_1(k2_wellord1(sK2,X2)))
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f226,f64])).

fof(f226,plain,(
    ! [X4] : r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X4) ),
    inference(superposition,[],[f217,f160])).

fof(f350,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k2_wellord1(sK2,X0)),k3_relat_1(k2_wellord1(sK2,X0))) ),
    inference(superposition,[],[f328,f158])).

fof(f328,plain,(
    ! [X10,X11] : r1_tarski(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X10),X11)),k3_relat_1(k2_wellord1(k2_wellord1(sK2,X10),X11))) ),
    inference(superposition,[],[f68,f258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (20363)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (20371)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (20360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (20385)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.51  % (20370)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (20358)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (20376)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.52  % (20369)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (20384)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (20380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (20381)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (20372)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (20367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (20362)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (20379)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (20357)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (20364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (20382)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.53  % (20378)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (20377)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (20359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (20361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.54  % (20387)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (20368)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (20386)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (20373)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.55  % (20383)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.55  % (20365)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.55  % (20374)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.56  % (20366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.56  % (20374)Refutation not found, incomplete strategy% (20374)------------------------------
% 1.49/0.56  % (20374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (20374)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (20374)Memory used [KB]: 10618
% 1.49/0.56  % (20374)Time elapsed: 0.150 s
% 1.49/0.56  % (20374)------------------------------
% 1.49/0.56  % (20374)------------------------------
% 1.61/0.61  % (20365)Refutation found. Thanks to Tanya!
% 1.61/0.61  % SZS status Theorem for theBenchmark
% 1.61/0.61  % SZS output start Proof for theBenchmark
% 1.61/0.61  fof(f762,plain,(
% 1.61/0.61    $false),
% 1.61/0.61    inference(avatar_sat_refutation,[],[f379,f386,f752])).
% 1.61/0.61  fof(f752,plain,(
% 1.61/0.61    ~spl4_9 | ~spl4_10),
% 1.61/0.61    inference(avatar_contradiction_clause,[],[f751])).
% 1.61/0.61  fof(f751,plain,(
% 1.61/0.61    $false | (~spl4_9 | ~spl4_10)),
% 1.61/0.61    inference(subsumption_resolution,[],[f750,f90])).
% 1.61/0.61  fof(f90,plain,(
% 1.61/0.61    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.61/0.61    inference(superposition,[],[f44,f72])).
% 1.61/0.61  fof(f72,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) )),
% 1.61/0.61    inference(resolution,[],[f42,f60])).
% 1.61/0.61  fof(f60,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f28])).
% 1.61/0.61  fof(f28,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.61/0.61    inference(ennf_transformation,[],[f15])).
% 1.61/0.61  fof(f15,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 1.61/0.61  fof(f42,plain,(
% 1.61/0.61    v1_relat_1(sK2)),
% 1.61/0.61    inference(cnf_transformation,[],[f35])).
% 1.61/0.61  fof(f35,plain,(
% 1.61/0.61    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.61/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f34])).
% 1.61/0.61  fof(f34,plain,(
% 1.61/0.61    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f19,plain,(
% 1.61/0.61    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.61/0.61    inference(flattening,[],[f18])).
% 1.61/0.61  fof(f18,plain,(
% 1.61/0.61    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.61/0.61    inference(ennf_transformation,[],[f17])).
% 1.61/0.61  fof(f17,negated_conjecture,(
% 1.61/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.61/0.61    inference(negated_conjecture,[],[f16])).
% 2.04/0.63  fof(f16,conjecture,(
% 2.04/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 2.04/0.63  fof(f44,plain,(
% 2.04/0.63    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 2.04/0.63    inference(cnf_transformation,[],[f35])).
% 2.04/0.63  fof(f750,plain,(
% 2.04/0.63    k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) | (~spl4_9 | ~spl4_10)),
% 2.04/0.63    inference(backward_demodulation,[],[f496,f749])).
% 2.04/0.63  fof(f749,plain,(
% 2.04/0.63    k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_9),
% 2.04/0.63    inference(subsumption_resolution,[],[f745,f373])).
% 2.04/0.63  fof(f373,plain,(
% 2.04/0.63    v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl4_9),
% 2.04/0.63    inference(avatar_component_clause,[],[f372])).
% 2.04/0.63  fof(f372,plain,(
% 2.04/0.63    spl4_9 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.04/0.63  fof(f745,plain,(
% 2.04/0.63    k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~v1_relat_1(k2_wellord1(sK2,sK0))),
% 2.04/0.63    inference(resolution,[],[f740,f51])).
% 2.04/0.63  fof(f51,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f24])).
% 2.04/0.63  fof(f24,plain,(
% 2.04/0.63    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(flattening,[],[f23])).
% 2.04/0.63  fof(f23,plain,(
% 2.04/0.63    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(ennf_transformation,[],[f10])).
% 2.04/0.63  fof(f10,axiom,(
% 2.04/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 2.04/0.63  fof(f740,plain,(
% 2.04/0.63    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 2.04/0.63    inference(superposition,[],[f719,f160])).
% 2.04/0.63  fof(f160,plain,(
% 2.04/0.63    ( ! [X1] : (k2_wellord1(sK2,X1) = k2_wellord1(k2_wellord1(sK2,X1),k3_relat_1(sK2))) )),
% 2.04/0.63    inference(superposition,[],[f72,f158])).
% 2.04/0.63  fof(f158,plain,(
% 2.04/0.63    sK2 = k2_wellord1(sK2,k3_relat_1(sK2))),
% 2.04/0.63    inference(forward_demodulation,[],[f157,f147])).
% 2.04/0.63  fof(f147,plain,(
% 2.04/0.63    sK2 = k8_relat_1(k3_relat_1(sK2),sK2)),
% 2.04/0.63    inference(subsumption_resolution,[],[f143,f42])).
% 2.04/0.63  fof(f143,plain,(
% 2.04/0.63    sK2 = k8_relat_1(k3_relat_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.04/0.63    inference(resolution,[],[f135,f51])).
% 2.04/0.63  fof(f135,plain,(
% 2.04/0.63    r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2))),
% 2.04/0.63    inference(resolution,[],[f110,f71])).
% 2.04/0.63  fof(f71,plain,(
% 2.04/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.04/0.63    inference(equality_resolution,[],[f53])).
% 2.04/0.63  fof(f53,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.04/0.63    inference(cnf_transformation,[],[f37])).
% 2.04/0.63  fof(f37,plain,(
% 2.04/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.63    inference(flattening,[],[f36])).
% 2.04/0.63  fof(f36,plain,(
% 2.04/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.63    inference(nnf_transformation,[],[f2])).
% 2.04/0.63  fof(f2,axiom,(
% 2.04/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.63  fof(f110,plain,(
% 2.04/0.63    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | r1_tarski(X0,k3_relat_1(sK2))) )),
% 2.04/0.63    inference(superposition,[],[f69,f74])).
% 2.04/0.63  fof(f74,plain,(
% 2.04/0.63    k3_relat_1(sK2) = k3_tarski(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 2.04/0.63    inference(resolution,[],[f42,f67])).
% 2.04/0.63  fof(f67,plain,(
% 2.04/0.63    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.04/0.63    inference(definition_unfolding,[],[f45,f66])).
% 2.04/0.63  fof(f66,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.04/0.63    inference(definition_unfolding,[],[f47,f65])).
% 2.04/0.63  fof(f65,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.04/0.63    inference(definition_unfolding,[],[f48,f59])).
% 2.04/0.63  fof(f59,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f7])).
% 2.04/0.63  fof(f7,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.04/0.63  fof(f48,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f6])).
% 2.04/0.63  fof(f6,axiom,(
% 2.04/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.04/0.63  fof(f47,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f8])).
% 2.04/0.63  fof(f8,axiom,(
% 2.04/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.04/0.63  fof(f45,plain,(
% 2.04/0.63    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f20])).
% 2.04/0.63  fof(f20,plain,(
% 2.04/0.63    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f9])).
% 2.04/0.63  fof(f9,axiom,(
% 2.04/0.63    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.04/0.63  fof(f69,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(definition_unfolding,[],[f63,f66])).
% 2.04/0.63  fof(f63,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f31])).
% 2.04/0.63  fof(f31,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.04/0.63    inference(ennf_transformation,[],[f3])).
% 2.04/0.63  fof(f3,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.04/0.63  fof(f157,plain,(
% 2.04/0.63    k8_relat_1(k3_relat_1(sK2),sK2) = k2_wellord1(sK2,k3_relat_1(sK2))),
% 2.04/0.63    inference(superposition,[],[f73,f116])).
% 2.04/0.63  fof(f116,plain,(
% 2.04/0.63    sK2 = k7_relat_1(sK2,k3_relat_1(sK2))),
% 2.04/0.63    inference(subsumption_resolution,[],[f112,f42])).
% 2.04/0.63  fof(f112,plain,(
% 2.04/0.63    sK2 = k7_relat_1(sK2,k3_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.04/0.63    inference(resolution,[],[f111,f52])).
% 2.04/0.63  fof(f52,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f26])).
% 2.04/0.63  fof(f26,plain,(
% 2.04/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(flattening,[],[f25])).
% 2.04/0.63  fof(f25,plain,(
% 2.04/0.63    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(ennf_transformation,[],[f11])).
% 2.04/0.63  fof(f11,axiom,(
% 2.04/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 2.04/0.63  fof(f111,plain,(
% 2.04/0.63    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2))),
% 2.04/0.63    inference(superposition,[],[f68,f74])).
% 2.04/0.63  fof(f68,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.04/0.63    inference(definition_unfolding,[],[f46,f66])).
% 2.04/0.63  fof(f46,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f5])).
% 2.04/0.63  fof(f5,axiom,(
% 2.04/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.04/0.63  fof(f73,plain,(
% 2.04/0.63    ( ! [X2] : (k2_wellord1(sK2,X2) = k8_relat_1(X2,k7_relat_1(sK2,X2))) )),
% 2.04/0.63    inference(resolution,[],[f42,f50])).
% 2.04/0.63  fof(f50,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 2.04/0.63    inference(cnf_transformation,[],[f22])).
% 2.04/0.63  fof(f22,plain,(
% 2.04/0.63    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.04/0.63    inference(ennf_transformation,[],[f13])).
% 2.04/0.63  fof(f13,axiom,(
% 2.04/0.63    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 2.04/0.63  fof(f719,plain,(
% 2.04/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k2_wellord1(k2_wellord1(sK2,sK0),X0)),sK1)) )),
% 2.04/0.63    inference(resolution,[],[f555,f71])).
% 2.04/0.63  fof(f555,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(k2_wellord1(k2_wellord1(sK2,sK0),X1))) | r1_tarski(X0,sK1)) )),
% 2.04/0.63    inference(resolution,[],[f325,f217])).
% 2.04/0.63  fof(f217,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X0)) )),
% 2.04/0.63    inference(duplicate_literal_removal,[],[f206])).
% 2.04/0.63  fof(f206,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X0) | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X0)) )),
% 2.04/0.63    inference(resolution,[],[f205,f58])).
% 2.04/0.63  fof(f58,plain,(
% 2.04/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f41])).
% 2.04/0.63  fof(f41,plain,(
% 2.04/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.04/0.63  fof(f40,plain,(
% 2.04/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.04/0.63    introduced(choice_axiom,[])).
% 2.04/0.63  fof(f39,plain,(
% 2.04/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(rectify,[],[f38])).
% 2.04/0.63  fof(f38,plain,(
% 2.04/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(nnf_transformation,[],[f27])).
% 2.04/0.63  fof(f27,plain,(
% 2.04/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.04/0.63    inference(ennf_transformation,[],[f1])).
% 2.04/0.63  fof(f1,axiom,(
% 2.04/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.04/0.63  fof(f205,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK3(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2),X0) | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2)) )),
% 2.04/0.63    inference(subsumption_resolution,[],[f203,f42])).
% 2.04/0.63  fof(f203,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK3(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2),X0) | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2) | ~v1_relat_1(sK2)) )),
% 2.04/0.63    inference(resolution,[],[f165,f49])).
% 2.04/0.63  fof(f49,plain,(
% 2.04/0.63    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f21])).
% 2.04/0.63  fof(f21,plain,(
% 2.04/0.63    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 2.04/0.63    inference(ennf_transformation,[],[f12])).
% 2.04/0.63  fof(f12,axiom,(
% 2.04/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 2.04/0.63  fof(f165,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(k2_wellord1(sK2,X1)) | r2_hidden(sK3(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2),X0) | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),X2)) )),
% 2.04/0.63    inference(resolution,[],[f92,f57])).
% 2.04/0.63  fof(f57,plain,(
% 2.04/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f41])).
% 2.04/0.63  fof(f92,plain,(
% 2.04/0.63    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_relat_1(k2_wellord1(k2_wellord1(sK2,X4),X3))) | r2_hidden(X5,X4) | ~v1_relat_1(k2_wellord1(sK2,X3))) )),
% 2.04/0.63    inference(superposition,[],[f62,f72])).
% 2.04/0.63  fof(f62,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f30])).
% 2.04/0.63  fof(f30,plain,(
% 2.04/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 2.04/0.63    inference(flattening,[],[f29])).
% 2.04/0.63  fof(f29,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.04/0.63    inference(ennf_transformation,[],[f14])).
% 2.04/0.63  fof(f14,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 2.04/0.63  fof(f325,plain,(
% 2.04/0.63    ( ! [X4,X2,X3] : (~r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X2),X3)),sK0) | r1_tarski(X4,sK1) | ~r1_tarski(X4,k2_relat_1(k2_wellord1(k2_wellord1(sK2,X2),X3)))) )),
% 2.04/0.63    inference(superposition,[],[f99,f258])).
% 2.04/0.63  fof(f258,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k2_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1))))) )),
% 2.04/0.63    inference(subsumption_resolution,[],[f256,f42])).
% 2.04/0.63  fof(f256,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)),k2_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1)))) | ~v1_relat_1(sK2)) )),
% 2.04/0.63    inference(resolution,[],[f140,f49])).
% 2.04/0.63  fof(f140,plain,(
% 2.04/0.63    ( ! [X8,X7] : (~v1_relat_1(k2_wellord1(sK2,X7)) | k3_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)),k1_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7)),k2_relat_1(k2_wellord1(k2_wellord1(sK2,X8),X7))))) )),
% 2.04/0.63    inference(resolution,[],[f93,f67])).
% 2.04/0.63  fof(f93,plain,(
% 2.04/0.63    ( ! [X6,X7] : (v1_relat_1(k2_wellord1(k2_wellord1(sK2,X7),X6)) | ~v1_relat_1(k2_wellord1(sK2,X6))) )),
% 2.04/0.63    inference(superposition,[],[f49,f72])).
% 2.04/0.63  fof(f99,plain,(
% 2.04/0.63    ( ! [X4,X2,X3] : (~r1_tarski(k3_tarski(k2_enumset1(X3,X3,X3,X4)),sK0) | r1_tarski(X2,sK1) | ~r1_tarski(X2,X4)) )),
% 2.04/0.63    inference(resolution,[],[f88,f69])).
% 2.04/0.63  fof(f88,plain,(
% 2.04/0.63    ( ! [X2,X3] : (~r1_tarski(X3,X2) | r1_tarski(X3,sK1) | ~r1_tarski(X2,sK0)) )),
% 2.04/0.63    inference(resolution,[],[f75,f64])).
% 2.04/0.63  fof(f64,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.04/0.63    inference(cnf_transformation,[],[f33])).
% 2.04/0.63  fof(f33,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.04/0.63    inference(flattening,[],[f32])).
% 2.04/0.63  fof(f32,plain,(
% 2.04/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.04/0.63    inference(ennf_transformation,[],[f4])).
% 2.04/0.63  fof(f4,axiom,(
% 2.04/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.04/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.04/0.63  fof(f75,plain,(
% 2.04/0.63    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0)) )),
% 2.04/0.63    inference(resolution,[],[f43,f64])).
% 2.04/0.63  fof(f43,plain,(
% 2.04/0.63    r1_tarski(sK0,sK1)),
% 2.04/0.63    inference(cnf_transformation,[],[f35])).
% 2.04/0.63  fof(f496,plain,(
% 2.04/0.63    k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_10),
% 2.04/0.63    inference(superposition,[],[f198,f378])).
% 2.04/0.63  fof(f378,plain,(
% 2.04/0.63    k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl4_10),
% 2.04/0.63    inference(avatar_component_clause,[],[f376])).
% 2.04/0.63  fof(f376,plain,(
% 2.04/0.63    spl4_10 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 2.04/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.04/0.63  fof(f198,plain,(
% 2.04/0.63    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k8_relat_1(X1,k7_relat_1(k2_wellord1(sK2,X0),X1))) )),
% 2.04/0.63    inference(superposition,[],[f197,f158])).
% 2.04/0.63  fof(f197,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2))) )),
% 2.04/0.63    inference(subsumption_resolution,[],[f195,f42])).
% 2.04/0.63  fof(f195,plain,(
% 2.04/0.63    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2) = k8_relat_1(X2,k7_relat_1(k2_wellord1(k2_wellord1(sK2,X0),X1),X2)) | ~v1_relat_1(sK2)) )),
% 2.04/0.63    inference(resolution,[],[f139,f49])).
% 2.04/0.63  fof(f139,plain,(
% 2.04/0.63    ( ! [X6,X4,X5] : (~v1_relat_1(k2_wellord1(sK2,X4)) | k2_wellord1(k2_wellord1(k2_wellord1(sK2,X5),X4),X6) = k8_relat_1(X6,k7_relat_1(k2_wellord1(k2_wellord1(sK2,X5),X4),X6))) )),
% 2.04/0.63    inference(resolution,[],[f93,f50])).
% 2.04/0.63  fof(f386,plain,(
% 2.04/0.63    spl4_9),
% 2.04/0.63    inference(avatar_contradiction_clause,[],[f385])).
% 2.04/0.63  fof(f385,plain,(
% 2.04/0.63    $false | spl4_9),
% 2.04/0.63    inference(subsumption_resolution,[],[f384,f42])).
% 2.04/0.63  fof(f384,plain,(
% 2.04/0.63    ~v1_relat_1(sK2) | spl4_9),
% 2.04/0.63    inference(resolution,[],[f374,f49])).
% 2.04/0.63  fof(f374,plain,(
% 2.04/0.63    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_9),
% 2.04/0.63    inference(avatar_component_clause,[],[f372])).
% 2.04/0.63  fof(f379,plain,(
% 2.04/0.63    ~spl4_9 | spl4_10),
% 2.04/0.63    inference(avatar_split_clause,[],[f369,f376,f372])).
% 2.04/0.63  fof(f369,plain,(
% 2.04/0.63    k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0))),
% 2.04/0.63    inference(resolution,[],[f355,f87])).
% 2.04/0.63  fof(f87,plain,(
% 2.04/0.63    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),sK0) | k7_relat_1(X1,sK1) = X1 | ~v1_relat_1(X1)) )),
% 2.04/0.63    inference(resolution,[],[f75,f52])).
% 2.04/0.63  fof(f355,plain,(
% 2.04/0.63    ( ! [X1] : (r1_tarski(k1_relat_1(k2_wellord1(sK2,X1)),X1)) )),
% 2.04/0.63    inference(resolution,[],[f350,f231])).
% 2.04/0.63  fof(f231,plain,(
% 2.04/0.63    ( ! [X2,X1] : (~r1_tarski(X1,k3_relat_1(k2_wellord1(sK2,X2))) | r1_tarski(X1,X2)) )),
% 2.04/0.63    inference(resolution,[],[f226,f64])).
% 2.04/0.63  fof(f226,plain,(
% 2.04/0.63    ( ! [X4] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X4)) )),
% 2.04/0.63    inference(superposition,[],[f217,f160])).
% 2.04/0.63  fof(f350,plain,(
% 2.04/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k2_wellord1(sK2,X0)),k3_relat_1(k2_wellord1(sK2,X0)))) )),
% 2.04/0.63    inference(superposition,[],[f328,f158])).
% 2.04/0.63  fof(f328,plain,(
% 2.04/0.63    ( ! [X10,X11] : (r1_tarski(k1_relat_1(k2_wellord1(k2_wellord1(sK2,X10),X11)),k3_relat_1(k2_wellord1(k2_wellord1(sK2,X10),X11)))) )),
% 2.04/0.63    inference(superposition,[],[f68,f258])).
% 2.04/0.63  % SZS output end Proof for theBenchmark
% 2.04/0.63  % (20365)------------------------------
% 2.04/0.63  % (20365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (20365)Termination reason: Refutation
% 2.04/0.63  
% 2.04/0.63  % (20365)Memory used [KB]: 11385
% 2.04/0.63  % (20365)Time elapsed: 0.207 s
% 2.04/0.63  % (20365)------------------------------
% 2.04/0.63  % (20365)------------------------------
% 2.04/0.63  % (20356)Success in time 0.276 s
%------------------------------------------------------------------------------
