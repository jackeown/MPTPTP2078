%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 302 expanded)
%              Number of leaves         :   25 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  311 ( 736 expanded)
%              Number of equality atoms :   93 ( 251 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1853,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f87,f406,f410,f415,f482,f648,f934,f1839])).

fof(f1839,plain,
    ( spl6_1
    | ~ spl6_3
    | ~ spl6_26
    | ~ spl6_59 ),
    inference(avatar_contradiction_clause,[],[f1838])).

fof(f1838,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | ~ spl6_26
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1837,f76])).

fof(f76,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1837,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_26
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1810,f631])).

fof(f631,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f629])).

fof(f629,plain,
    ( spl6_26
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1810,plain,
    ( k7_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f611,f1804,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1804,plain,
    ( ! [X0] : ~ r2_hidden(X0,k7_relat_1(sK1,sK0))
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1803,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1803,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k7_relat_1(sK1,sK0))
        | ~ r1_xboole_0(k7_relat_1(sK1,sK0),k1_xboole_0) )
    | ~ spl6_59 ),
    inference(superposition,[],[f64,f933])).

fof(f933,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k1_xboole_0))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f931])).

fof(f931,plain,
    ( spl6_59
  <=> k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f611,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(sK1,k1_xboole_0))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f601,f69])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f601,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f42,f269])).

fof(f269,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X4)))
        | ~ r1_xboole_0(k1_relat_1(sK1),X4) )
    | ~ spl6_3 ),
    inference(superposition,[],[f64,f88])).

fof(f88,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f86,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f86,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f934,plain,
    ( spl6_59
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f929,f271,f84,f931])).

fof(f271,plain,
    ( spl6_15
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f929,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f920,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f920,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0)))))
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(superposition,[],[f124,f273])).

fof(f273,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f271])).

fof(f124,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X0),k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f89,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f43,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f89,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f648,plain,
    ( spl6_26
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f623,f107,f84,f78,f629])).

fof(f78,plain,
    ( spl6_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f107,plain,
    ( spl6_5
  <=> k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f623,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f601,f236])).

fof(f236,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_xboole_0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f230,f40])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f230,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = X0
        | r2_hidden(sK3(k1_xboole_0,X0),X0) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(resolution,[],[f217,f55])).

fof(f217,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f101,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f79,f64])).

fof(f79,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f482,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f476,f78,f107])).

fof(f476,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f415,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f218,f107,f78])).

fof(f218,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f109,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f410,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f261,f107,f84,f271])).

fof(f261,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f88,f109])).

fof(f406,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | spl6_5 ),
    inference(subsumption_resolution,[],[f404,f40])).

fof(f404,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_5 ),
    inference(forward_demodulation,[],[f392,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f392,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl6_3
    | spl6_5 ),
    inference(superposition,[],[f108,f88])).

fof(f108,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f82,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f38,f78,f74])).

fof(f38,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f39,f78,f74])).

fof(f39,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (3645)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (3659)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (3661)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (3651)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (3639)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (3644)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (3647)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (3641)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (3648)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (3637)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (3640)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (3636)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (3658)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (3650)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (3635)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (3653)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (3646)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (3658)Refutation not found, incomplete strategy% (3658)------------------------------
% 0.20/0.53  % (3658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3658)Memory used [KB]: 10746
% 0.20/0.53  % (3658)Time elapsed: 0.080 s
% 0.20/0.53  % (3658)------------------------------
% 0.20/0.53  % (3658)------------------------------
% 0.20/0.53  % (3643)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (3653)Refutation not found, incomplete strategy% (3653)------------------------------
% 0.20/0.53  % (3653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3653)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3653)Memory used [KB]: 10618
% 0.20/0.53  % (3653)Time elapsed: 0.121 s
% 0.20/0.53  % (3653)------------------------------
% 0.20/0.53  % (3653)------------------------------
% 0.20/0.53  % (3642)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (3660)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (3664)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (3656)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (3662)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (3652)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (3657)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (3661)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (3654)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (3655)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (3663)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (3649)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.56  % (3665)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f1853,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f81,f82,f87,f406,f410,f415,f482,f648,f934,f1839])).
% 1.56/0.57  fof(f1839,plain,(
% 1.56/0.57    spl6_1 | ~spl6_3 | ~spl6_26 | ~spl6_59),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f1838])).
% 1.56/0.57  fof(f1838,plain,(
% 1.56/0.57    $false | (spl6_1 | ~spl6_3 | ~spl6_26 | ~spl6_59)),
% 1.56/0.57    inference(subsumption_resolution,[],[f1837,f76])).
% 1.56/0.57  fof(f76,plain,(
% 1.56/0.57    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl6_1),
% 1.56/0.57    inference(avatar_component_clause,[],[f74])).
% 1.56/0.57  fof(f74,plain,(
% 1.56/0.57    spl6_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.56/0.57  fof(f1837,plain,(
% 1.56/0.57    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl6_3 | ~spl6_26 | ~spl6_59)),
% 1.56/0.57    inference(forward_demodulation,[],[f1810,f631])).
% 1.56/0.57  fof(f631,plain,(
% 1.56/0.57    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | ~spl6_26),
% 1.56/0.57    inference(avatar_component_clause,[],[f629])).
% 1.56/0.57  fof(f629,plain,(
% 1.56/0.57    spl6_26 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.56/0.57  fof(f1810,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | (~spl6_3 | ~spl6_59)),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f611,f1804,f55])).
% 1.56/0.57  fof(f55,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f34])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.56/0.57    inference(rectify,[],[f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.56/0.57  fof(f1804,plain,(
% 1.56/0.57    ( ! [X0] : (~r2_hidden(X0,k7_relat_1(sK1,sK0))) ) | ~spl6_59),
% 1.56/0.57    inference(subsumption_resolution,[],[f1803,f42])).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.56/0.57  fof(f1803,plain,(
% 1.56/0.57    ( ! [X0] : (~r2_hidden(X0,k7_relat_1(sK1,sK0)) | ~r1_xboole_0(k7_relat_1(sK1,sK0),k1_xboole_0)) ) | ~spl6_59),
% 1.56/0.57    inference(superposition,[],[f64,f933])).
% 1.56/0.57  fof(f933,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k1_xboole_0)) | ~spl6_59),
% 1.56/0.57    inference(avatar_component_clause,[],[f931])).
% 1.56/0.57  fof(f931,plain,(
% 1.56/0.57    spl6_59 <=> k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k1_xboole_0))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 1.56/0.57  fof(f64,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.56/0.57    inference(definition_unfolding,[],[f48,f62])).
% 1.56/0.57  fof(f62,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.56/0.57    inference(definition_unfolding,[],[f45,f61])).
% 1.56/0.57  fof(f61,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f46,f60])).
% 1.56/0.57  fof(f60,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.57  fof(f45,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.56/0.57    inference(ennf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.57    inference(rectify,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.56/0.57  fof(f611,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k7_relat_1(sK1,k1_xboole_0))) ) | ~spl6_3),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f601,f69])).
% 1.56/0.57  fof(f69,plain,(
% 1.56/0.57    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.56/0.57    inference(equality_resolution,[],[f54])).
% 1.56/0.57  fof(f54,plain,(
% 1.56/0.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f34])).
% 1.56/0.57  fof(f601,plain,(
% 1.56/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))) ) | ~spl6_3),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f42,f269])).
% 1.56/0.57  fof(f269,plain,(
% 1.56/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X4))) | ~r1_xboole_0(k1_relat_1(sK1),X4)) ) | ~spl6_3),
% 1.56/0.57    inference(superposition,[],[f64,f88])).
% 1.56/0.57  fof(f88,plain,(
% 1.56/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0))) ) | ~spl6_3),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f86,f66])).
% 1.56/0.57  fof(f66,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f50,f62])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f21])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.56/0.57  fof(f86,plain,(
% 1.56/0.57    v1_relat_1(sK1) | ~spl6_3),
% 1.56/0.57    inference(avatar_component_clause,[],[f84])).
% 1.56/0.57  fof(f84,plain,(
% 1.56/0.57    spl6_3 <=> v1_relat_1(sK1)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.56/0.57  fof(f934,plain,(
% 1.56/0.57    spl6_59 | ~spl6_3 | ~spl6_15),
% 1.56/0.57    inference(avatar_split_clause,[],[f929,f271,f84,f931])).
% 1.56/0.57  fof(f271,plain,(
% 1.56/0.57    spl6_15 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.56/0.57  fof(f929,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k1_xboole_0)) | (~spl6_3 | ~spl6_15)),
% 1.56/0.57    inference(forward_demodulation,[],[f920,f72])).
% 1.56/0.57  fof(f72,plain,(
% 1.56/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.56/0.57    inference(equality_resolution,[],[f58])).
% 1.56/0.57  fof(f58,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f36])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.56/0.57    inference(flattening,[],[f35])).
% 1.56/0.57  fof(f35,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.56/0.57  fof(f920,plain,(
% 1.56/0.57    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0))))) | (~spl6_3 | ~spl6_15)),
% 1.56/0.57    inference(superposition,[],[f124,f273])).
% 1.56/0.57  fof(f273,plain,(
% 1.56/0.57    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl6_15),
% 1.56/0.57    inference(avatar_component_clause,[],[f271])).
% 1.56/0.57  fof(f124,plain,(
% 1.56/0.57    ( ! [X0] : (k7_relat_1(sK1,X0) = k1_setfam_1(k2_enumset1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X0),k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))))) ) | ~spl6_3),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f89,f63])).
% 1.56/0.57  fof(f63,plain,(
% 1.56/0.57    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f43,f62])).
% 1.56/0.57  fof(f43,plain,(
% 1.56/0.57    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f18])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,axiom,(
% 1.56/0.57    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.56/0.57  fof(f89,plain,(
% 1.56/0.57    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl6_3),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f86,f49])).
% 1.56/0.57  fof(f49,plain,(
% 1.56/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f20])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.56/0.57  fof(f648,plain,(
% 1.56/0.57    spl6_26 | ~spl6_2 | ~spl6_3 | ~spl6_5),
% 1.56/0.57    inference(avatar_split_clause,[],[f623,f107,f84,f78,f629])).
% 1.56/0.57  fof(f78,plain,(
% 1.56/0.57    spl6_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.56/0.57  fof(f107,plain,(
% 1.56/0.57    spl6_5 <=> k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.56/0.57  fof(f623,plain,(
% 1.56/0.57    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.56/0.57    inference(resolution,[],[f601,f236])).
% 1.56/0.57  fof(f236,plain,(
% 1.56/0.57    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) ) | (~spl6_2 | ~spl6_5)),
% 1.56/0.57    inference(forward_demodulation,[],[f230,f40])).
% 1.56/0.57  fof(f40,plain,(
% 1.56/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.57    inference(cnf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,axiom,(
% 1.56/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.56/0.57  fof(f230,plain,(
% 1.56/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = X0 | r2_hidden(sK3(k1_xboole_0,X0),X0)) ) | (~spl6_2 | ~spl6_5)),
% 1.56/0.57    inference(resolution,[],[f217,f55])).
% 1.56/0.57  fof(f217,plain,(
% 1.56/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_5)),
% 1.56/0.57    inference(backward_demodulation,[],[f101,f109])).
% 1.56/0.57  fof(f109,plain,(
% 1.56/0.57    k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) | ~spl6_5),
% 1.56/0.57    inference(avatar_component_clause,[],[f107])).
% 1.56/0.57  fof(f101,plain,(
% 1.56/0.57    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))) ) | ~spl6_2),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f79,f64])).
% 1.56/0.57  fof(f79,plain,(
% 1.56/0.57    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl6_2),
% 1.56/0.57    inference(avatar_component_clause,[],[f78])).
% 1.56/0.57  fof(f482,plain,(
% 1.56/0.57    spl6_5 | ~spl6_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f476,f78,f107])).
% 1.56/0.57  fof(f476,plain,(
% 1.56/0.57    k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) | ~spl6_2),
% 1.56/0.57    inference(resolution,[],[f79,f68])).
% 1.56/0.57  fof(f68,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f51,f62])).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.56/0.57  fof(f415,plain,(
% 1.56/0.57    spl6_2 | ~spl6_5),
% 1.56/0.57    inference(avatar_split_clause,[],[f218,f107,f78])).
% 1.56/0.57  fof(f218,plain,(
% 1.56/0.57    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl6_5),
% 1.56/0.57    inference(unit_resulting_resolution,[],[f109,f67])).
% 1.56/0.57  fof(f67,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.56/0.57    inference(definition_unfolding,[],[f52,f62])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f28])).
% 1.56/0.57  fof(f410,plain,(
% 1.56/0.57    spl6_15 | ~spl6_3 | ~spl6_5),
% 1.56/0.57    inference(avatar_split_clause,[],[f261,f107,f84,f271])).
% 1.56/0.57  fof(f261,plain,(
% 1.56/0.57    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl6_3 | ~spl6_5)),
% 1.56/0.57    inference(superposition,[],[f88,f109])).
% 1.56/0.57  fof(f406,plain,(
% 1.56/0.57    ~spl6_1 | ~spl6_3 | spl6_5),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f405])).
% 1.56/0.57  fof(f405,plain,(
% 1.56/0.57    $false | (~spl6_1 | ~spl6_3 | spl6_5)),
% 1.56/0.57    inference(subsumption_resolution,[],[f404,f40])).
% 1.56/0.57  fof(f404,plain,(
% 1.56/0.57    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl6_1 | ~spl6_3 | spl6_5)),
% 1.56/0.57    inference(forward_demodulation,[],[f392,f75])).
% 1.56/0.57  fof(f75,plain,(
% 1.56/0.57    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl6_1),
% 1.56/0.57    inference(avatar_component_clause,[],[f74])).
% 1.56/0.57  fof(f392,plain,(
% 1.56/0.57    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl6_3 | spl6_5)),
% 1.56/0.57    inference(superposition,[],[f108,f88])).
% 1.56/0.57  fof(f108,plain,(
% 1.56/0.57    k1_xboole_0 != k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) | spl6_5),
% 1.56/0.57    inference(avatar_component_clause,[],[f107])).
% 1.56/0.57  fof(f87,plain,(
% 1.56/0.57    spl6_3),
% 1.56/0.57    inference(avatar_split_clause,[],[f37,f84])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    v1_relat_1(sK1)),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.56/0.57    inference(flattening,[],[f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.56/0.57    inference(negated_conjecture,[],[f14])).
% 1.56/0.57  fof(f14,conjecture,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.56/0.57  fof(f82,plain,(
% 1.56/0.57    spl6_1 | spl6_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f38,f78,f74])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f81,plain,(
% 1.56/0.57    ~spl6_1 | ~spl6_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f39,f78,f74])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (3661)------------------------------
% 1.56/0.57  % (3661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (3661)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (3661)Memory used [KB]: 7419
% 1.56/0.57  % (3661)Time elapsed: 0.120 s
% 1.56/0.57  % (3661)------------------------------
% 1.56/0.57  % (3661)------------------------------
% 1.56/0.57  % (3634)Success in time 0.213 s
%------------------------------------------------------------------------------
