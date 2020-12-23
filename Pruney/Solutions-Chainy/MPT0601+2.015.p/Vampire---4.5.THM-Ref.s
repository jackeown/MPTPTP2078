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
% DateTime   : Thu Dec  3 12:51:09 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 244 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  266 ( 629 expanded)
%              Number of equality atoms :   82 ( 247 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f93,f167,f209])).

fof(f209,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f207,f47])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f207,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f206,f168])).

fof(f168,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0))
    | ~ spl4_1 ),
    inference(resolution,[],[f86,f148])).

fof(f148,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_xboole_0(X4,k4_enumset1(X3,X3,X3,X3,X3,X5)) ) ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f72,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f86,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f206,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f61,f194])).

fof(f194,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f192,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f192,plain,
    ( ! [X0] : ~ r2_hidden(X0,k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f191,f151])).

fof(f151,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f147,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f147,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f191,plain,
    ( r1_tarski(k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f189,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f189,plain,
    ( r1_tarski(k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0))
    | ~ spl4_2 ),
    inference(superposition,[],[f184,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f184,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))),k11_relat_1(sK1,X0))) ),
    inference(superposition,[],[f180,f159])).

fof(f159,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f79,f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f180,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK1,X0))) ),
    inference(subsumption_resolution,[],[f179,f47])).

fof(f179,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK1,X0)))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f173,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f173,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(resolution,[],[f95,f47])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f167,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f165,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f165,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | spl4_2 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1))
    | spl4_2 ),
    inference(superposition,[],[f90,f163])).

fof(f163,plain,(
    ! [X1] :
      ( k1_xboole_0 = k11_relat_1(sK1,X1)
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(backward_demodulation,[],[f144,f159])).

fof(f144,plain,(
    ! [X1] :
      ( k1_xboole_0 = k9_relat_1(sK1,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f143,f51])).

fof(f51,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f143,plain,(
    ! [X1] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f139,plain,(
    ! [X1] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(sK1)
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f60,f137])).

fof(f137,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f80,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f56,f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f90,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f93,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f89,f85])).

fof(f48,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f49,f89,f85])).

fof(f49,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9751)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (9767)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (9745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (9751)Refutation not found, incomplete strategy% (9751)------------------------------
% 0.21/0.51  % (9751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9751)Memory used [KB]: 10618
% 0.21/0.52  % (9751)Time elapsed: 0.102 s
% 0.21/0.52  % (9751)------------------------------
% 0.21/0.52  % (9751)------------------------------
% 0.21/0.52  % (9746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (9759)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (9749)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (9756)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (9757)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (9744)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  % (9744)Refutation not found, incomplete strategy% (9744)------------------------------
% 1.34/0.53  % (9744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9744)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (9744)Memory used [KB]: 10746
% 1.34/0.53  % (9744)Time elapsed: 0.114 s
% 1.34/0.53  % (9744)------------------------------
% 1.34/0.53  % (9744)------------------------------
% 1.34/0.53  % (9768)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.53  % (9765)Refutation not found, incomplete strategy% (9765)------------------------------
% 1.34/0.53  % (9765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9765)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (9765)Memory used [KB]: 10618
% 1.34/0.53  % (9765)Time elapsed: 0.088 s
% 1.34/0.53  % (9765)------------------------------
% 1.34/0.53  % (9765)------------------------------
% 1.34/0.53  % (9764)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.53  % (9748)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.53  % (9743)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (9754)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (9754)Refutation not found, incomplete strategy% (9754)------------------------------
% 1.34/0.53  % (9754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9754)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.54  % (9754)Memory used [KB]: 10618
% 1.34/0.54  % (9754)Time elapsed: 0.128 s
% 1.34/0.54  % (9754)------------------------------
% 1.34/0.54  % (9754)------------------------------
% 1.34/0.54  % (9745)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f212,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f92,f93,f167,f209])).
% 1.34/0.54  fof(f209,plain,(
% 1.34/0.54    ~spl4_1 | ~spl4_2),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 1.34/0.54  fof(f208,plain,(
% 1.34/0.54    $false | (~spl4_1 | ~spl4_2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f207,f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    v1_relat_1(sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.34/0.54    inference(flattening,[],[f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.34/0.54    inference(negated_conjecture,[],[f20])).
% 1.34/0.54  fof(f20,conjecture,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.34/0.54  fof(f207,plain,(
% 1.34/0.54    ~v1_relat_1(sK1) | (~spl4_1 | ~spl4_2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f206,f168])).
% 1.34/0.54  fof(f168,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0))) ) | ~spl4_1),
% 1.34/0.54    inference(resolution,[],[f86,f148])).
% 1.34/0.54  fof(f148,plain,(
% 1.34/0.54    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~r1_xboole_0(X4,k4_enumset1(X3,X3,X3,X3,X3,X5))) )),
% 1.34/0.54    inference(resolution,[],[f81,f64])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.34/0.54  fof(f81,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f72,f77])).
% 1.34/0.54  fof(f77,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f58,f76])).
% 1.34/0.54  fof(f76,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f71,f75])).
% 1.34/0.54  fof(f75,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f73,f74])).
% 1.34/0.54  fof(f74,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.34/0.54  fof(f73,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.54  fof(f71,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f72,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.34/0.54  fof(f86,plain,(
% 1.34/0.54    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl4_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f85])).
% 1.34/0.54  fof(f85,plain,(
% 1.34/0.54    spl4_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.34/0.54  fof(f206,plain,(
% 1.34/0.54    r1_xboole_0(k1_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_2),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f203])).
% 1.34/0.54  fof(f203,plain,(
% 1.34/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_2),
% 1.34/0.54    inference(superposition,[],[f61,f194])).
% 1.34/0.54  fof(f194,plain,(
% 1.34/0.54    k1_xboole_0 = k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_2),
% 1.34/0.54    inference(resolution,[],[f192,f57])).
% 1.34/0.54  fof(f57,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.34/0.54    inference(ennf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.34/0.54  fof(f192,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl4_2),
% 1.34/0.54    inference(resolution,[],[f191,f151])).
% 1.34/0.54  fof(f151,plain,(
% 1.34/0.54    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 1.34/0.54    inference(resolution,[],[f147,f65])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f44])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f42,plain,(
% 1.34/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.54    inference(rectify,[],[f41])).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.54    inference(nnf_transformation,[],[f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.54  fof(f147,plain,(
% 1.34/0.54    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.34/0.54    inference(resolution,[],[f81,f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.34/0.54  fof(f191,plain,(
% 1.34/0.54    r1_tarski(k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) | ~spl4_2),
% 1.34/0.54    inference(forward_demodulation,[],[f189,f82])).
% 1.34/0.54  fof(f82,plain,(
% 1.34/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.34/0.54    inference(equality_resolution,[],[f70])).
% 1.34/0.54  fof(f70,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f46])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.34/0.54    inference(flattening,[],[f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.34/0.54    inference(nnf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.34/0.54  fof(f189,plain,(
% 1.34/0.54    r1_tarski(k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)) | ~spl4_2),
% 1.34/0.54    inference(superposition,[],[f184,f91])).
% 1.34/0.54  fof(f91,plain,(
% 1.34/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl4_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f89])).
% 1.34/0.54  fof(f89,plain,(
% 1.34/0.54    spl4_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.34/0.54  fof(f184,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))),k11_relat_1(sK1,X0)))) )),
% 1.34/0.54    inference(superposition,[],[f180,f159])).
% 1.34/0.54  fof(f159,plain,(
% 1.34/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 1.34/0.54    inference(resolution,[],[f79,f47])).
% 1.34/0.54  fof(f79,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f55,f78])).
% 1.34/0.54  fof(f78,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f53,f77])).
% 1.34/0.54  fof(f53,plain,(
% 1.34/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.34/0.54  fof(f180,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK1,X0)))) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f179,f47])).
% 1.34/0.54  fof(f179,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(sK1,X0))) | ~v1_relat_1(sK1)) )),
% 1.34/0.54    inference(superposition,[],[f173,f60])).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.34/0.54  fof(f173,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0))))) )),
% 1.34/0.54    inference(resolution,[],[f95,f47])).
% 1.34/0.54  fof(f95,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1))))) )),
% 1.34/0.54    inference(resolution,[],[f54,f59])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.34/0.54  fof(f167,plain,(
% 1.34/0.54    spl4_1 | spl4_2),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f166])).
% 1.34/0.54  fof(f166,plain,(
% 1.34/0.54    $false | (spl4_1 | spl4_2)),
% 1.34/0.54    inference(subsumption_resolution,[],[f165,f87])).
% 1.34/0.54  fof(f87,plain,(
% 1.34/0.54    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl4_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f85])).
% 1.34/0.54  fof(f165,plain,(
% 1.34/0.54    r2_hidden(sK0,k1_relat_1(sK1)) | spl4_2),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f164])).
% 1.34/0.54  fof(f164,plain,(
% 1.34/0.54    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1)) | spl4_2),
% 1.34/0.54    inference(superposition,[],[f90,f163])).
% 1.34/0.54  fof(f163,plain,(
% 1.34/0.54    ( ! [X1] : (k1_xboole_0 = k11_relat_1(sK1,X1) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 1.34/0.54    inference(backward_demodulation,[],[f144,f159])).
% 1.34/0.54  fof(f144,plain,(
% 1.34/0.54    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k4_enumset1(X1,X1,X1,X1,X1,X1)) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 1.34/0.54    inference(forward_demodulation,[],[f143,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,axiom,(
% 1.34/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.34/0.54  fof(f143,plain,(
% 1.34/0.54    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k4_enumset1(X1,X1,X1,X1,X1,X1)) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f139,f47])).
% 1.34/0.54  fof(f139,plain,(
% 1.34/0.54    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k4_enumset1(X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(sK1) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 1.34/0.54    inference(superposition,[],[f60,f137])).
% 1.34/0.54  fof(f137,plain,(
% 1.34/0.54    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.34/0.54    inference(resolution,[],[f80,f104])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 1.34/0.54    inference(resolution,[],[f56,f47])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f63,f78])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.34/0.54  fof(f90,plain,(
% 1.34/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl4_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f89])).
% 1.34/0.54  fof(f93,plain,(
% 1.34/0.54    spl4_1 | ~spl4_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f48,f89,f85])).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 1.34/0.54    inference(cnf_transformation,[],[f37])).
% 1.34/0.54  fof(f92,plain,(
% 1.34/0.54    ~spl4_1 | spl4_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f49,f89,f85])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.34/0.54    inference(cnf_transformation,[],[f37])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (9745)------------------------------
% 1.34/0.54  % (9745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (9745)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (9745)Memory used [KB]: 10874
% 1.34/0.54  % (9745)Time elapsed: 0.130 s
% 1.34/0.54  % (9745)------------------------------
% 1.34/0.54  % (9745)------------------------------
% 1.34/0.54  % (9770)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (9741)Success in time 0.179 s
%------------------------------------------------------------------------------
