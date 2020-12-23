%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 316 expanded)
%              Number of leaves         :   19 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  220 ( 779 expanded)
%              Number of equality atoms :   92 ( 426 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f189,f269])).

% (4481)Refutation not found, incomplete strategy% (4481)------------------------------
% (4481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4481)Termination reason: Refutation not found, incomplete strategy

% (4481)Memory used [KB]: 10874
% (4481)Time elapsed: 0.034 s
% (4481)------------------------------
% (4481)------------------------------
fof(f269,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f255,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f255,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f80,f246])).

fof(f246,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f229,f65])).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f229,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f108,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f108,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_3
  <=> r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,(
    ~ v1_xboole_0(k1_relat_1(sK1)) ),
    inference(superposition,[],[f64,f63])).

fof(f63,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f37,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f26])).

fof(f26,plain,
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

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f189,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f188,f107,f111])).

fof(f111,plain,
    ( spl3_4
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f188,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | k1_xboole_0 != k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f165,f63])).

fof(f165,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f131,f120])).

fof(f120,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f119,f72])).

fof(f72,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f35,f78])).

fof(f78,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k11_relat_1(X2,sK0) = k9_relat_1(X2,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f66,f63])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f131,plain,(
    ! [X1] :
      ( k1_xboole_0 != k11_relat_1(sK1,X1)
      | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,(
    ! [X1] :
      ( k1_xboole_0 != k11_relat_1(sK1,X1)
      | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f66])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f185,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f182,f180])).

fof(f180,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1)
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f121,f154])).

fof(f154,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f152,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X1),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f55,f120])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f121,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f62,f112,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f112,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f62,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f38,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f182,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1)
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f35,f36,f122,f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f122,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f62,f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (4479)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.48  % (4481)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.48  % (4487)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.49  % (4487)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f185,f189,f269])).
% 0.20/0.49  % (4481)Refutation not found, incomplete strategy% (4481)------------------------------
% 0.20/0.49  % (4481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4481)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4481)Memory used [KB]: 10874
% 0.20/0.49  % (4481)Time elapsed: 0.034 s
% 0.20/0.49  % (4481)------------------------------
% 0.20/0.49  % (4481)------------------------------
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ~spl3_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f268])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    $false | ~spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f255,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.20/0.50    inference(backward_demodulation,[],[f80,f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK1) | ~spl3_3),
% 0.20/0.50    inference(superposition,[],[f229,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.50    inference(definition_unfolding,[],[f41,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f42,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f46,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1))) | ~spl3_3),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f108,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f49,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f45,f59])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl3_3 <=> r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_relat_1(sK1))),
% 0.20/0.50    inference(superposition,[],[f64,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.50    inference(definition_unfolding,[],[f37,f61])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f15])).
% 0.20/0.50  fof(f15,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f40,f61])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ~spl3_4 | spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f188,f107,f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl3_4 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | k1_xboole_0 != k2_relat_1(sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f165,f63])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.50    inference(superposition,[],[f131,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f119,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f35,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f35,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2] : (~v1_relat_1(X2) | k11_relat_1(X2,sK0) = k9_relat_1(X2,k1_relat_1(sK1))) )),
% 0.20/0.50    inference(superposition,[],[f66,f63])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f44,f61])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 != k11_relat_1(sK1,X1) | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f127,f35])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 != k11_relat_1(sK1,X1) | r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f47,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f35,f66])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f184])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    $false | spl3_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f182,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1) | spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f121,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X1),sK1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f35])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X1),sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.50    inference(superposition,[],[f55,f120])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(nnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f62,f112,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.20/0.50    inference(definition_unfolding,[],[f51,f61])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK1) | spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.50    inference(definition_unfolding,[],[f38,f61])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK0,sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),sK1) | spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f35,f36,f122,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(nnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f62,f112,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.20/0.50    inference(definition_unfolding,[],[f52,f61])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (4487)------------------------------
% 0.20/0.50  % (4487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4487)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (4487)Memory used [KB]: 10746
% 0.20/0.50  % (4487)Time elapsed: 0.078 s
% 0.20/0.50  % (4487)------------------------------
% 0.20/0.50  % (4487)------------------------------
% 0.20/0.51  % (4456)Success in time 0.149 s
%------------------------------------------------------------------------------
