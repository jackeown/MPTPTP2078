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
% DateTime   : Thu Dec  3 12:50:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 250 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 ( 948 expanded)
%              Number of equality atoms :   39 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f84,f95,f136,f142,f166,f177,f456,f509,f724,f1370])).

fof(f1370,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f1369])).

fof(f1369,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f1350,f690])).

fof(f690,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f165,f625])).

fof(f625,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f622,f98])).

fof(f98,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f44,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f622,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,sK1),k1_xboole_0)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f213,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_2
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X2,sK1),k10_relat_1(sK1,X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X2)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f115,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(X0,X1,sK1),X0),sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f70,f74])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f61,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
            & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f165,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_6
  <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1350,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f176,f723,f600])).

fof(f600,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(X0,k9_relat_1(sK1,X1))
        | ~ r2_hidden(sK4(X0,k1_relat_1(sK1),sK1),X1) )
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(superposition,[],[f211,f94])).

fof(f94,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_4
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
        | r2_hidden(X0,k9_relat_1(sK1,X2))
        | ~ r2_hidden(sK4(X0,X1,sK1),X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f114,f112])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,k9_relat_1(sK1,X1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f69,f74])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f723,plain,
    ( r2_hidden(sK4(sK3(k2_relat_1(sK1),sK0),k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl6_17
  <=> r2_hidden(sK4(sK3(k2_relat_1(sK1),sK0),k1_relat_1(sK1),sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f176,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_7
  <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f724,plain,
    ( spl6_17
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f317,f174,f92,f72,f721])).

fof(f317,plain,
    ( r2_hidden(sK4(sK3(k2_relat_1(sK1),sK0),k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f176,f195])).

fof(f195,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0,k1_relat_1(sK1),sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(superposition,[],[f100,f94])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
        | r2_hidden(sK4(X0,X1,sK1),X1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f56,f74])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f509,plain,
    ( ~ spl6_3
    | spl6_9 ),
    inference(avatar_split_clause,[],[f283,f216,f81])).

fof(f81,plain,
    ( spl6_3
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f216,plain,
    ( spl6_9
  <=> r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f283,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f218,f230])).

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK3(X3,X4),X2)
      | ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f218,plain,
    ( ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f216])).

fof(f456,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f449,f344])).

fof(f344,plain,
    ( r2_hidden(sK5(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f74,f135,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f135,plain,
    ( r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_5
  <=> r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f449,plain,
    ( ~ r2_hidden(sK5(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f135,f217,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k10_relat_1(X1,X2))
      | ~ r1_xboole_0(X3,k2_relat_1(X1))
      | ~ r2_hidden(sK5(X0,X2,X1),X3) ) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f217,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f216])).

fof(f177,plain,
    ( spl6_7
    | spl6_3 ),
    inference(avatar_split_clause,[],[f144,f81,f174])).

fof(f144,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f82,f48])).

fof(f82,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f166,plain,
    ( spl6_6
    | spl6_3 ),
    inference(avatar_split_clause,[],[f143,f81,f163])).

fof(f143,plain,
    ( r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f82,f49])).

fof(f142,plain,
    ( ~ spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f141,f77,f81])).

fof(f141,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f43,f79])).

fof(f43,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f136,plain,
    ( spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f85,f77,f133])).

fof(f85,plain,
    ( r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f78,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f95,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f86,f72,f92])).

fof(f86,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f84,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f42,f81,f77])).

fof(f42,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f41,f72])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (2536)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (2536)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f1374,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f75,f84,f95,f136,f142,f166,f177,f456,f509,f724,f1370])).
% 0.22/0.47  fof(f1370,plain,(
% 0.22/0.47    ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_17),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f1369])).
% 0.22/0.47  fof(f1369,plain,(
% 0.22/0.47    $false | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_17)),
% 0.22/0.47    inference(subsumption_resolution,[],[f1350,f690])).
% 0.22/0.47  fof(f690,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(sK3(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_6)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f165,f625])).
% 0.22/0.47  fof(f625,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f622,f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f44,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f62,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f47,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f51,f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f63,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.47  fof(f622,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,sK1),k1_xboole_0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) ) | (~spl6_1 | ~spl6_2)),
% 0.22/0.47    inference(superposition,[],[f213,f79])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl6_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl6_2 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.47  fof(f213,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X2,sK1),k10_relat_1(sK1,X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK1,X2))) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f115,f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f55,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    v1_relat_1(sK1) | ~spl6_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f72])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    spl6_1 <=> v1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(rectify,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(nnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k10_relat_1(sK1,X1))) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f70,f74])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f61,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(flattening,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(rectify,[],[f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(nnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.47  fof(f165,plain,(
% 0.22/0.47    r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0) | ~spl6_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f163])).
% 0.22/0.47  fof(f163,plain,(
% 0.22/0.47    spl6_6 <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.47  fof(f1350,plain,(
% 0.22/0.47    r2_hidden(sK3(k2_relat_1(sK1),sK0),k9_relat_1(sK1,k1_relat_1(sK1))) | (~spl6_1 | ~spl6_4 | ~spl6_7 | ~spl6_17)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f176,f723,f600])).
% 0.22/0.47  fof(f600,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(sK4(X0,k1_relat_1(sK1),sK1),X1)) ) | (~spl6_1 | ~spl6_4)),
% 0.22/0.47    inference(superposition,[],[f211,f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) | ~spl6_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    spl6_4 <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.47  fof(f211,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | r2_hidden(X0,k9_relat_1(sK1,X2)) | ~r2_hidden(sK4(X0,X1,sK1),X2)) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f114,f112])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k9_relat_1(sK1,X1))) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f69,f74])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f57,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f36])).
% 0.22/0.47  fof(f723,plain,(
% 0.22/0.47    r2_hidden(sK4(sK3(k2_relat_1(sK1),sK0),k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | ~spl6_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f721])).
% 0.22/0.47  fof(f721,plain,(
% 0.22/0.47    spl6_17 <=> r2_hidden(sK4(sK3(k2_relat_1(sK1),sK0),k1_relat_1(sK1),sK1),k1_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.47  fof(f176,plain,(
% 0.22/0.47    r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | ~spl6_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f174])).
% 0.22/0.47  fof(f174,plain,(
% 0.22/0.47    spl6_7 <=> r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.47  fof(f724,plain,(
% 0.22/0.47    spl6_17 | ~spl6_1 | ~spl6_4 | ~spl6_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f317,f174,f92,f72,f721])).
% 0.22/0.47  fof(f317,plain,(
% 0.22/0.47    r2_hidden(sK4(sK3(k2_relat_1(sK1),sK0),k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | (~spl6_1 | ~spl6_4 | ~spl6_7)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f176,f195])).
% 0.22/0.47  fof(f195,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK4(X0,k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (~spl6_1 | ~spl6_4)),
% 0.22/0.47    inference(superposition,[],[f100,f94])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | r2_hidden(sK4(X0,X1,sK1),X1)) ) | ~spl6_1),
% 0.22/0.47    inference(resolution,[],[f56,f74])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f36])).
% 0.22/0.47  fof(f509,plain,(
% 0.22/0.47    ~spl6_3 | spl6_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f283,f216,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl6_3 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.47  fof(f216,plain,(
% 0.22/0.47    spl6_9 <=> r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.47  fof(f283,plain,(
% 0.22/0.47    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl6_9),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f218,f230])).
% 0.22/0.47  fof(f230,plain,(
% 0.22/0.47    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f227])).
% 0.22/0.47  fof(f227,plain,(
% 0.22/0.47    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.47    inference(resolution,[],[f89,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X4,X2,X3] : (~r2_hidden(sK3(X3,X4),X2) | ~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X4)) )),
% 0.22/0.48    inference(resolution,[],[f50,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,k2_relat_1(sK1)) | spl6_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f216])).
% 0.22/0.48  fof(f456,plain,(
% 0.22/0.48    ~spl6_1 | ~spl6_5 | ~spl6_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f455])).
% 0.22/0.48  fof(f455,plain,(
% 0.22/0.48    $false | (~spl6_1 | ~spl6_5 | ~spl6_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f449,f344])).
% 0.22/0.48  fof(f344,plain,(
% 0.22/0.48    r2_hidden(sK5(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),sK0) | (~spl6_1 | ~spl6_5)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f74,f135,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) | ~spl6_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl6_5 <=> r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.48  fof(f449,plain,(
% 0.22/0.48    ~r2_hidden(sK5(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),sK0) | (~spl6_1 | ~spl6_5 | ~spl6_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f74,f135,f217,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k10_relat_1(X1,X2)) | ~r1_xboole_0(X3,k2_relat_1(X1)) | ~r2_hidden(sK5(X0,X2,X1),X3)) )),
% 0.22/0.48    inference(resolution,[],[f58,f50])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f40])).
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl6_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f216])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    spl6_7 | spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f144,f81,f174])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    r2_hidden(sK3(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f82,f48])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f81])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    spl6_6 | spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f143,f81,f163])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    r2_hidden(sK3(k2_relat_1(sK1),sK0),sK0) | spl6_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f82,f49])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ~spl6_3 | ~spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f141,f77,f81])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f43,f79])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f13])).
% 0.22/0.48  fof(f13,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl6_5 | spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f85,f77,f133])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) | spl6_2),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f78,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl6_4 | ~spl6_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f86,f72,f92])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) | ~spl6_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f74,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl6_2 | spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f42,f81,f77])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl6_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f72])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (2536)------------------------------
% 0.22/0.48  % (2536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2536)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (2536)Memory used [KB]: 11385
% 0.22/0.48  % (2536)Time elapsed: 0.069 s
% 0.22/0.48  % (2536)------------------------------
% 0.22/0.48  % (2536)------------------------------
% 0.22/0.48  % (2520)Success in time 0.12 s
%------------------------------------------------------------------------------
