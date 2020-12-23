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
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 310 expanded)
%              Number of leaves         :   27 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  298 ( 792 expanded)
%              Number of equality atoms :   51 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f101,f133,f288,f468,f995,f1075,f1171,f1266])).

fof(f1266,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(avatar_contradiction_clause,[],[f1265])).

fof(f1265,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f1258,f748])).

fof(f748,plain,
    ( ! [X28,X29] : r1_xboole_0(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f747,f164])).

fof(f164,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f81,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f100,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f100,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_5
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f78,f36])).

fof(f78,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK1))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f66,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f747,plain,
    ( ! [X28,X29] :
        ( r2_hidden(sK4(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28)),k1_xboole_0)
        | r1_xboole_0(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28)) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f724,f206])).

fof(f206,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f162,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f162,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f87,f153])).

fof(f87,plain,
    ( ! [X0] : r1_xboole_0(X0,k3_xboole_0(sK1,sK2))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f724,plain,
    ( ! [X28,X29] :
        ( r2_hidden(sK4(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28)),k3_xboole_0(X29,k1_xboole_0))
        | r1_xboole_0(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28)) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(superposition,[],[f122,f281])).

fof(f281,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK1,X0))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f155,f268])).

fof(f268,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f163,f46])).

fof(f163,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f84,f153])).

fof(f84,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(sK1,sK2),X0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f155,plain,
    ( ! [X0] : k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl6_5 ),
    inference(superposition,[],[f49,f100])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,X2)))
      | r1_xboole_0(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f39,f49])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1258,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f473,f1243])).

fof(f1243,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,X0)))
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f1170,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f1170,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1168,plain,
    ( spl6_25
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f473,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f467,f467,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f467,plain,
    ( r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl6_14
  <=> r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1171,plain,
    ( spl6_25
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1088,f1072,f1168])).

fof(f1072,plain,
    ( spl6_22
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1088,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f1074,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1074,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1075,plain,
    ( spl6_22
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f1025,f992,f285,f98,f64,f1072])).

fof(f285,plain,
    ( spl6_11
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f992,plain,
    ( spl6_21
  <=> k1_xboole_0 = k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1025,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f1024,f268])).

fof(f1024,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f1023,f36])).

fof(f1023,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(backward_demodulation,[],[f289,f998])).

fof(f998,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_21 ),
    inference(superposition,[],[f994,f36])).

fof(f994,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f992])).

fof(f289,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl6_11 ),
    inference(superposition,[],[f287,f49])).

fof(f287,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f285])).

fof(f995,plain,
    ( spl6_21
    | spl6_6 ),
    inference(avatar_split_clause,[],[f478,f130,f992])).

fof(f130,plain,
    ( spl6_6
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f478,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f132,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f132,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f468,plain,
    ( spl6_14
    | spl6_3 ),
    inference(avatar_split_clause,[],[f114,f69,f465])).

fof(f69,plain,
    ( spl6_3
  <=> r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f114,plain,
    ( r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))))
    | spl6_3 ),
    inference(forward_demodulation,[],[f107,f36])).

fof(f107,plain,
    ( r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f71,f39])).

fof(f71,plain,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f288,plain,
    ( spl6_11
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f90,f74,f285])).

fof(f74,plain,
    ( spl6_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f90,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f76,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f133,plain,
    ( ~ spl6_6
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f102,f64,f59,f130])).

fof(f59,plain,
    ( spl6_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f102,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f61,f66,f43])).

fof(f61,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f101,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f92,f64,f98])).

fof(f92,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f66,f46])).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f74])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f31,f53])).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f72,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f54,f69])).

fof(f54,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (23474)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (23490)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (23487)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (23475)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (23473)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (23486)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (23482)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (23478)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (23481)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (23488)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (23480)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (23479)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (23485)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (23477)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (23484)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (23489)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (23483)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (23476)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.54  % (23488)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1271,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f101,f133,f288,f468,f995,f1075,f1171,f1266])).
% 0.21/0.54  fof(f1266,plain,(
% 0.21/0.54    ~spl6_2 | ~spl6_5 | ~spl6_14 | ~spl6_25),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1265])).
% 0.21/0.54  fof(f1265,plain,(
% 0.21/0.54    $false | (~spl6_2 | ~spl6_5 | ~spl6_14 | ~spl6_25)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1258,f748])).
% 0.21/0.54  fof(f748,plain,(
% 0.21/0.54    ( ! [X28,X29] : (r1_xboole_0(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28))) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f747,f164])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(backward_demodulation,[],[f81,f153])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl6_5),
% 0.21/0.54    inference(superposition,[],[f100,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl6_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl6_5 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) ) | ~spl6_2),
% 0.21/0.54    inference(forward_demodulation,[],[f78,f36])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK1))) ) | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f747,plain,(
% 0.21/0.54    ( ! [X28,X29] : (r2_hidden(sK4(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28)),k1_xboole_0) | r1_xboole_0(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28))) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(forward_demodulation,[],[f724,f206])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f162,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(backward_demodulation,[],[f87,f153])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK1,sK2))) ) | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f81,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f724,plain,(
% 0.21/0.54    ( ! [X28,X29] : (r2_hidden(sK4(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28)),k3_xboole_0(X29,k1_xboole_0)) | r1_xboole_0(k3_xboole_0(X29,sK2),k3_xboole_0(sK1,X28))) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(superposition,[],[f122,f281])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK1,X0))) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(backward_demodulation,[],[f155,f268])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f163,f46])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.54    inference(backward_demodulation,[],[f84,f153])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK1,sK2),X0)) ) | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f81,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0] : (k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_5),
% 0.21/0.54    inference(superposition,[],[f49,f100])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,X2))) | r1_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.54    inference(superposition,[],[f39,f49])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f1258,plain,(
% 0.21/0.54    ~r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | (~spl6_14 | ~spl6_25)),
% 0.21/0.54    inference(backward_demodulation,[],[f473,f1243])).
% 0.21/0.54  fof(f1243,plain,(
% 0.21/0.54    ( ! [X0] : (k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,X0)))) ) | ~spl6_25),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f1170,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f50,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.54  fof(f1170,plain,(
% 0.21/0.54    r1_xboole_0(sK1,sK0) | ~spl6_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f1168])).
% 0.21/0.54  fof(f1168,plain,(
% 0.21/0.54    spl6_25 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.54  fof(f473,plain,(
% 0.21/0.54    ~r1_xboole_0(k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))) | ~spl6_14),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f467,f467,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))) | ~spl6_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f465])).
% 0.21/0.54  fof(f465,plain,(
% 0.21/0.54    spl6_14 <=> r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.54  fof(f1171,plain,(
% 0.21/0.54    spl6_25 | ~spl6_22),
% 0.21/0.54    inference(avatar_split_clause,[],[f1088,f1072,f1168])).
% 0.21/0.54  fof(f1072,plain,(
% 0.21/0.54    spl6_22 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.54  fof(f1088,plain,(
% 0.21/0.54    r1_xboole_0(sK1,sK0) | ~spl6_22),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f1074,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(superposition,[],[f47,f36])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f1074,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl6_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f1072])).
% 0.21/0.54  fof(f1075,plain,(
% 0.21/0.54    spl6_22 | ~spl6_2 | ~spl6_5 | ~spl6_11 | ~spl6_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f1025,f992,f285,f98,f64,f1072])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    spl6_11 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.54  fof(f992,plain,(
% 0.21/0.54    spl6_21 <=> k1_xboole_0 = k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.54  fof(f1025,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl6_2 | ~spl6_5 | ~spl6_11 | ~spl6_21)),
% 0.21/0.54    inference(forward_demodulation,[],[f1024,f268])).
% 0.21/0.54  fof(f1024,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) | (~spl6_11 | ~spl6_21)),
% 0.21/0.54    inference(forward_demodulation,[],[f1023,f36])).
% 0.21/0.54  fof(f1023,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) | (~spl6_11 | ~spl6_21)),
% 0.21/0.54    inference(backward_demodulation,[],[f289,f998])).
% 0.21/0.54  fof(f998,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_21),
% 0.21/0.54    inference(superposition,[],[f994,f36])).
% 0.21/0.54  fof(f994,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | ~spl6_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f992])).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k3_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))) | ~spl6_11),
% 0.21/0.54    inference(superposition,[],[f287,f49])).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f285])).
% 0.21/0.54  fof(f995,plain,(
% 0.21/0.54    spl6_21 | spl6_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f478,f130,f992])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl6_6 <=> r2_hidden(sK3,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.54  fof(f478,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | spl6_6),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f132,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.21/0.54    inference(resolution,[],[f56,f46])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f44,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f51])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~r2_hidden(sK3,sK1) | spl6_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f130])).
% 0.21/0.54  fof(f468,plain,(
% 0.21/0.54    spl6_14 | spl6_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f69,f465])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl6_3 <=> r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))) | spl6_3),
% 0.21/0.54    inference(forward_demodulation,[],[f107,f36])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    r2_hidden(sK4(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1),k3_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)) | spl6_3),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f71,f39])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) | spl6_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    spl6_11 | ~spl6_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f90,f74,f285])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    spl6_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_4),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f76,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f74])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ~spl6_6 | ~spl6_1 | ~spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f102,f64,f59,f130])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl6_1 <=> r2_hidden(sK3,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ~r2_hidden(sK3,sK1) | (~spl6_1 | ~spl6_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f61,f66,f43])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    r2_hidden(sK3,sK2) | ~spl6_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl6_5 | ~spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f92,f64,f98])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl6_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f46])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl6_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f55,f74])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f53])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ~spl6_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f69])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f34,f52])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f64])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl6_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f59])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    r2_hidden(sK3,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23488)------------------------------
% 0.21/0.54  % (23488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23488)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23488)Memory used [KB]: 11769
% 0.21/0.54  % (23488)Time elapsed: 0.082 s
% 0.21/0.54  % (23488)------------------------------
% 0.21/0.54  % (23488)------------------------------
% 0.21/0.54  % (23470)Success in time 0.179 s
%------------------------------------------------------------------------------
