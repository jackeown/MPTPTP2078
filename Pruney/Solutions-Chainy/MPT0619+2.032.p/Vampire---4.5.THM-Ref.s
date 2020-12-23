%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:50 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 307 expanded)
%              Number of leaves         :   19 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 ( 784 expanded)
%              Number of equality atoms :   92 ( 415 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f129,f143,f177])).

fof(f177,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f174,f151])).

fof(f151,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f37,f38,f128,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f128,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_5
  <=> k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f110,f140])).

fof(f140,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK0,X1),sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f136,f37])).

fof(f136,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X1),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f53,f96])).

fof(f96,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f95,f74])).

fof(f74,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f95,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f37,f81])).

fof(f81,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k11_relat_1(X2,sK0) = k9_relat_1(X2,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,(
    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f110,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_2
  <=> r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f143,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f142,f104])).

fof(f104,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f142,plain,(
    k1_xboole_0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f141,f37])).

fof(f141,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f137,f97])).

fof(f97,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f92,f82])).

fof(f82,plain,(
    ! [X3] :
      ( r2_hidden(sK0,X3)
      | ~ r1_tarski(k1_relat_1(sK1),X3) ) ),
    inference(superposition,[],[f71,f65])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f92,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f46,f73])).

fof(f73,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f137,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f47,f96])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f129,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f124,f126,f104])).

fof(f124,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X1] :
      ( k2_relat_1(sK1) != X1
      | k1_funct_1(sK1,sK0) != sK2(X1,k1_funct_1(sK1,sK0))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f64,plain,(
    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f40,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f102,f108,f104])).

fof(f102,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) != X0
      | r2_hidden(sK2(X0,k1_funct_1(sK1,sK0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f64,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24339)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (24341)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (24336)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (24328)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.51  % (24331)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.19/0.51  % (24323)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.19/0.51  % (24323)Refutation not found, incomplete strategy% (24323)------------------------------
% 1.19/0.51  % (24323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (24313)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.19/0.51  % (24333)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.51  % (24339)Refutation found. Thanks to Tanya!
% 1.19/0.51  % SZS status Theorem for theBenchmark
% 1.19/0.51  % (24323)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (24323)Memory used [KB]: 10618
% 1.19/0.51  % (24323)Time elapsed: 0.112 s
% 1.19/0.51  % (24323)------------------------------
% 1.19/0.51  % (24323)------------------------------
% 1.19/0.51  % (24314)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.51  % (24328)Refutation not found, incomplete strategy% (24328)------------------------------
% 1.19/0.51  % (24328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (24328)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (24328)Memory used [KB]: 6268
% 1.19/0.51  % (24328)Time elapsed: 0.078 s
% 1.19/0.51  % (24328)------------------------------
% 1.19/0.51  % (24328)------------------------------
% 1.19/0.52  % (24316)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.52  % (24318)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.52  % (24326)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.52  % SZS output start Proof for theBenchmark
% 1.19/0.52  fof(f178,plain,(
% 1.19/0.52    $false),
% 1.19/0.52    inference(avatar_sat_refutation,[],[f111,f129,f143,f177])).
% 1.19/0.52  fof(f177,plain,(
% 1.19/0.52    ~spl3_2 | spl3_5),
% 1.19/0.52    inference(avatar_contradiction_clause,[],[f176])).
% 1.19/0.52  fof(f176,plain,(
% 1.19/0.52    $false | (~spl3_2 | spl3_5)),
% 1.19/0.52    inference(subsumption_resolution,[],[f174,f151])).
% 1.19/0.52  fof(f151,plain,(
% 1.19/0.52    ~r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1) | spl3_5),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f37,f38,f128,f55])).
% 1.19/0.52  fof(f55,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f34])).
% 1.19/0.52  fof(f34,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(flattening,[],[f33])).
% 1.19/0.52  fof(f33,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(nnf_transformation,[],[f26])).
% 1.19/0.52  fof(f26,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(flattening,[],[f25])).
% 1.19/0.52  fof(f25,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.19/0.52    inference(ennf_transformation,[],[f13])).
% 1.19/0.52  fof(f13,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.19/0.52  fof(f128,plain,(
% 1.19/0.52    k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl3_5),
% 1.19/0.52    inference(avatar_component_clause,[],[f126])).
% 1.19/0.52  fof(f126,plain,(
% 1.19/0.52    spl3_5 <=> k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.19/0.52  fof(f38,plain,(
% 1.19/0.52    v1_funct_1(sK1)),
% 1.19/0.52    inference(cnf_transformation,[],[f28])).
% 1.19/0.52  fof(f28,plain,(
% 1.19/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).
% 1.19/0.52  fof(f27,plain,(
% 1.19/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f17,plain,(
% 1.19/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.19/0.52    inference(flattening,[],[f16])).
% 1.19/0.52  fof(f16,plain,(
% 1.19/0.52    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.19/0.52    inference(ennf_transformation,[],[f15])).
% 1.19/0.52  fof(f15,negated_conjecture,(
% 1.19/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.19/0.52    inference(negated_conjecture,[],[f14])).
% 1.19/0.52  fof(f14,conjecture,(
% 1.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.19/0.52  fof(f37,plain,(
% 1.19/0.52    v1_relat_1(sK1)),
% 1.19/0.52    inference(cnf_transformation,[],[f28])).
% 1.19/0.52  fof(f174,plain,(
% 1.19/0.52    r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1) | ~spl3_2),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f110,f140])).
% 1.19/0.52  fof(f140,plain,(
% 1.19/0.52    ( ! [X1] : (r2_hidden(k4_tarski(sK0,X1),sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.19/0.52    inference(subsumption_resolution,[],[f136,f37])).
% 1.19/0.52  fof(f136,plain,(
% 1.19/0.52    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X1),sK1) | ~v1_relat_1(sK1)) )),
% 1.19/0.52    inference(superposition,[],[f53,f96])).
% 1.19/0.52  fof(f96,plain,(
% 1.19/0.52    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 1.19/0.52    inference(forward_demodulation,[],[f95,f74])).
% 1.19/0.52  fof(f74,plain,(
% 1.19/0.52    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f37,f43])).
% 1.19/0.52  fof(f43,plain,(
% 1.19/0.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f19])).
% 1.19/0.52  fof(f19,plain,(
% 1.19/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f8])).
% 1.19/0.52  fof(f8,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.19/0.52  fof(f95,plain,(
% 1.19/0.52    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f37,f81])).
% 1.19/0.52  fof(f81,plain,(
% 1.19/0.52    ( ! [X2] : (~v1_relat_1(X2) | k11_relat_1(X2,sK0) = k9_relat_1(X2,k1_relat_1(sK1))) )),
% 1.19/0.52    inference(superposition,[],[f66,f65])).
% 1.19/0.52  fof(f65,plain,(
% 1.19/0.52    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.19/0.52    inference(definition_unfolding,[],[f39,f63])).
% 1.19/0.52  fof(f63,plain,(
% 1.19/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.19/0.52    inference(definition_unfolding,[],[f41,f62])).
% 1.19/0.52  fof(f62,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.19/0.52    inference(definition_unfolding,[],[f45,f61])).
% 1.19/0.52  fof(f61,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.19/0.52    inference(definition_unfolding,[],[f51,f60])).
% 1.19/0.52  fof(f60,plain,(
% 1.19/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f4])).
% 1.19/0.52  fof(f4,axiom,(
% 1.19/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.19/0.52  fof(f51,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f3])).
% 1.19/0.52  fof(f3,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.19/0.52  fof(f45,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f2])).
% 1.19/0.52  fof(f2,axiom,(
% 1.19/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.19/0.52  fof(f41,plain,(
% 1.19/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f1])).
% 1.19/0.52  fof(f1,axiom,(
% 1.19/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.52  fof(f39,plain,(
% 1.19/0.52    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.19/0.52    inference(cnf_transformation,[],[f28])).
% 1.19/0.52  fof(f66,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(definition_unfolding,[],[f44,f63])).
% 1.19/0.52  fof(f44,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f20])).
% 1.19/0.52  fof(f20,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f7])).
% 1.19/0.52  fof(f7,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.19/0.52  fof(f53,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f32])).
% 1.19/0.52  fof(f32,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(nnf_transformation,[],[f24])).
% 1.19/0.52  fof(f24,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.19/0.52    inference(ennf_transformation,[],[f9])).
% 1.19/0.52  fof(f9,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.19/0.52  fof(f110,plain,(
% 1.19/0.52    r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | ~spl3_2),
% 1.19/0.52    inference(avatar_component_clause,[],[f108])).
% 1.19/0.52  fof(f108,plain,(
% 1.19/0.52    spl3_2 <=> r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.19/0.52  fof(f143,plain,(
% 1.19/0.52    ~spl3_1),
% 1.19/0.52    inference(avatar_split_clause,[],[f142,f104])).
% 1.19/0.52  fof(f104,plain,(
% 1.19/0.52    spl3_1 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.19/0.52  fof(f142,plain,(
% 1.19/0.52    k1_xboole_0 != k2_relat_1(sK1)),
% 1.19/0.52    inference(subsumption_resolution,[],[f141,f37])).
% 1.19/0.52  fof(f141,plain,(
% 1.19/0.52    k1_xboole_0 != k2_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.19/0.52    inference(subsumption_resolution,[],[f137,f97])).
% 1.19/0.52  fof(f97,plain,(
% 1.19/0.52    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f92,f82])).
% 1.19/0.52  fof(f82,plain,(
% 1.19/0.52    ( ! [X3] : (r2_hidden(sK0,X3) | ~r1_tarski(k1_relat_1(sK1),X3)) )),
% 1.19/0.52    inference(superposition,[],[f71,f65])).
% 1.19/0.52  fof(f71,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 1.19/0.52    inference(definition_unfolding,[],[f57,f62])).
% 1.19/0.52  fof(f57,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f36])).
% 1.19/0.52  fof(f36,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.19/0.52    inference(flattening,[],[f35])).
% 1.19/0.52  fof(f35,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.19/0.52    inference(nnf_transformation,[],[f5])).
% 1.19/0.52  fof(f5,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.19/0.52  fof(f92,plain,(
% 1.19/0.52    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.19/0.52    inference(subsumption_resolution,[],[f91,f37])).
% 1.19/0.52  fof(f91,plain,(
% 1.19/0.52    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.19/0.52    inference(superposition,[],[f46,f73])).
% 1.19/0.52  fof(f73,plain,(
% 1.19/0.52    sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f37,f42])).
% 1.19/0.52  fof(f42,plain,(
% 1.19/0.52    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  fof(f18,plain,(
% 1.19/0.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f12])).
% 1.19/0.52  fof(f12,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 1.19/0.52  fof(f46,plain,(
% 1.19/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f21])).
% 1.19/0.52  fof(f21,plain,(
% 1.19/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f11])).
% 1.19/0.52  fof(f11,axiom,(
% 1.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.19/0.52  fof(f137,plain,(
% 1.19/0.52    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.19/0.52    inference(superposition,[],[f47,f96])).
% 1.19/0.52  fof(f47,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f29])).
% 1.19/0.52  fof(f29,plain,(
% 1.19/0.52    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(nnf_transformation,[],[f22])).
% 1.19/0.52  fof(f22,plain,(
% 1.19/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f10])).
% 1.19/0.52  fof(f10,axiom,(
% 1.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 1.19/0.52  fof(f129,plain,(
% 1.19/0.52    spl3_1 | ~spl3_5),
% 1.19/0.52    inference(avatar_split_clause,[],[f124,f126,f104])).
% 1.19/0.52  fof(f124,plain,(
% 1.19/0.52    k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | k1_xboole_0 = k2_relat_1(sK1)),
% 1.19/0.52    inference(equality_resolution,[],[f88])).
% 1.19/0.52  fof(f88,plain,(
% 1.19/0.52    ( ! [X1] : (k2_relat_1(sK1) != X1 | k1_funct_1(sK1,sK0) != sK2(X1,k1_funct_1(sK1,sK0)) | k1_xboole_0 = X1) )),
% 1.19/0.52    inference(superposition,[],[f64,f67])).
% 1.19/0.52  fof(f67,plain,(
% 1.19/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.19/0.52    inference(definition_unfolding,[],[f50,f63])).
% 1.19/0.52  fof(f50,plain,(
% 1.19/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.19/0.52    inference(cnf_transformation,[],[f31])).
% 1.19/0.52  fof(f31,plain,(
% 1.19/0.52    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f30])).
% 1.19/0.52  fof(f30,plain,(
% 1.19/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f23,plain,(
% 1.19/0.52    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.19/0.52    inference(ennf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,axiom,(
% 1.19/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.19/0.52  fof(f64,plain,(
% 1.19/0.52    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.19/0.52    inference(definition_unfolding,[],[f40,f63])).
% 1.19/0.52  fof(f40,plain,(
% 1.19/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.19/0.52    inference(cnf_transformation,[],[f28])).
% 1.19/0.52  fof(f111,plain,(
% 1.19/0.52    spl3_1 | spl3_2),
% 1.19/0.52    inference(avatar_split_clause,[],[f102,f108,f104])).
% 1.19/0.52  fof(f102,plain,(
% 1.19/0.52    r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1)),
% 1.19/0.52    inference(equality_resolution,[],[f87])).
% 1.19/0.52  fof(f87,plain,(
% 1.19/0.52    ( ! [X0] : (k2_relat_1(sK1) != X0 | r2_hidden(sK2(X0,k1_funct_1(sK1,sK0)),X0) | k1_xboole_0 = X0) )),
% 1.19/0.52    inference(superposition,[],[f64,f68])).
% 1.19/0.52  fof(f68,plain,(
% 1.19/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.19/0.52    inference(definition_unfolding,[],[f49,f63])).
% 1.19/0.52  fof(f49,plain,(
% 1.19/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.19/0.52    inference(cnf_transformation,[],[f31])).
% 1.19/0.52  % SZS output end Proof for theBenchmark
% 1.19/0.52  % (24339)------------------------------
% 1.19/0.52  % (24339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (24339)Termination reason: Refutation
% 1.19/0.52  
% 1.19/0.52  % (24339)Memory used [KB]: 10746
% 1.19/0.52  % (24339)Time elapsed: 0.115 s
% 1.19/0.52  % (24339)------------------------------
% 1.19/0.52  % (24339)------------------------------
% 1.19/0.52  % (24325)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.52  % (24312)Success in time 0.164 s
%------------------------------------------------------------------------------
