%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:57 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 233 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 ( 600 expanded)
%              Number of equality atoms :   45 ( 127 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1097,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f202,f277,f281,f1016,f1096])).

fof(f1096,plain,
    ( spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f1095])).

fof(f1095,plain,
    ( $false
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1094,f38])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f1094,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1086,f39])).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f1086,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | spl4_8
    | ~ spl4_9 ),
    inference(resolution,[],[f1079,f387])).

fof(f387,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) ) ),
    inference(resolution,[],[f70,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f1079,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl4_8
    | ~ spl4_9 ),
    inference(resolution,[],[f1078,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1078,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1071,f196])).

fof(f196,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_9
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1071,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_8 ),
    inference(resolution,[],[f1028,f106])).

fof(f106,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1028,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl4_8 ),
    inference(resolution,[],[f193,f57])).

fof(f193,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_8
  <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1016,plain,
    ( ~ spl4_9
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f1015])).

fof(f1015,plain,
    ( $false
    | ~ spl4_9
    | spl4_16 ),
    inference(subsumption_resolution,[],[f1014,f39])).

fof(f1014,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl4_9
    | spl4_16 ),
    inference(subsumption_resolution,[],[f995,f38])).

fof(f995,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl4_9
    | spl4_16 ),
    inference(resolution,[],[f387,f357])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_9
    | spl4_16 ),
    inference(resolution,[],[f344,f57])).

fof(f344,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_9
    | spl4_16 ),
    inference(subsumption_resolution,[],[f338,f196])).

fof(f338,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_16 ),
    inference(resolution,[],[f288,f105])).

fof(f105,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f72,f60])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f58,f58])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl4_16 ),
    inference(resolution,[],[f276,f57])).

fof(f276,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl4_16
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f281,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f278,f38])).

fof(f278,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(resolution,[],[f197,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f197,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f195])).

fof(f277,plain,
    ( ~ spl4_9
    | ~ spl4_16
    | spl4_10 ),
    inference(avatar_split_clause,[],[f270,f199,f274,f195])).

fof(f199,plain,
    ( spl4_10
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f270,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_10 ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_10 ),
    inference(superposition,[],[f201,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f201,plain,
    ( k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f202,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f135,f199,f195,f191])).

fof(f135,plain,
    ( k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    inference(superposition,[],[f97,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k8_relat_1(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k8_relat_1(X1,X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f97,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f40,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f40,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:00:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (11308)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (11300)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (11291)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (11282)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (11297)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (11285)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11286)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (11305)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (11306)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (11294)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (11295)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (11290)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (11281)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (11289)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (11283)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (11307)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (11304)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (11284)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (11288)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (11298)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (11311)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (11293)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11287)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (11299)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (11292)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (11299)Refutation not found, incomplete strategy% (11299)------------------------------
% 0.20/0.53  % (11299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11299)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11299)Memory used [KB]: 10618
% 0.20/0.53  % (11299)Time elapsed: 0.131 s
% 0.20/0.53  % (11299)------------------------------
% 0.20/0.53  % (11299)------------------------------
% 0.20/0.54  % (11302)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (11309)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (11310)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (11301)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (11303)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (11304)Refutation not found, incomplete strategy% (11304)------------------------------
% 0.20/0.55  % (11304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11304)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11304)Memory used [KB]: 10746
% 0.20/0.55  % (11304)Time elapsed: 0.150 s
% 0.20/0.55  % (11304)------------------------------
% 0.20/0.55  % (11304)------------------------------
% 1.94/0.60  % (11309)Refutation found. Thanks to Tanya!
% 1.94/0.60  % SZS status Theorem for theBenchmark
% 1.94/0.61  % SZS output start Proof for theBenchmark
% 1.94/0.61  fof(f1097,plain,(
% 1.94/0.61    $false),
% 1.94/0.61    inference(avatar_sat_refutation,[],[f202,f277,f281,f1016,f1096])).
% 1.94/0.62  fof(f1096,plain,(
% 1.94/0.62    spl4_8 | ~spl4_9),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f1095])).
% 1.94/0.62  fof(f1095,plain,(
% 1.94/0.62    $false | (spl4_8 | ~spl4_9)),
% 1.94/0.62    inference(subsumption_resolution,[],[f1094,f38])).
% 1.94/0.62  fof(f38,plain,(
% 1.94/0.62    v1_relat_1(sK2)),
% 1.94/0.62    inference(cnf_transformation,[],[f33])).
% 1.94/0.62  fof(f33,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32])).
% 1.94/0.62  fof(f32,plain,(
% 1.94/0.62    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f18,plain,(
% 1.94/0.62    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.94/0.62    inference(flattening,[],[f17])).
% 1.94/0.62  fof(f17,plain,(
% 1.94/0.62    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.94/0.62    inference(ennf_transformation,[],[f16])).
% 1.94/0.62  fof(f16,negated_conjecture,(
% 1.94/0.62    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.94/0.62    inference(negated_conjecture,[],[f15])).
% 1.94/0.62  fof(f15,conjecture,(
% 1.94/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 1.94/0.62  fof(f1094,plain,(
% 1.94/0.62    ~v1_relat_1(sK2) | (spl4_8 | ~spl4_9)),
% 1.94/0.62    inference(subsumption_resolution,[],[f1086,f39])).
% 1.94/0.62  fof(f39,plain,(
% 1.94/0.62    r1_tarski(sK0,sK1)),
% 1.94/0.62    inference(cnf_transformation,[],[f33])).
% 1.94/0.62  fof(f1086,plain,(
% 1.94/0.62    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK2) | (spl4_8 | ~spl4_9)),
% 1.94/0.62    inference(resolution,[],[f1079,f387])).
% 1.94/0.62  fof(f387,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(duplicate_literal_removal,[],[f377])).
% 1.94/0.62  fof(f377,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)) )),
% 1.94/0.62    inference(resolution,[],[f70,f52])).
% 1.94/0.62  fof(f52,plain,(
% 1.94/0.62    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f37])).
% 1.94/0.62  fof(f37,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.94/0.62  fof(f36,plain,(
% 1.94/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.94/0.62    introduced(choice_axiom,[])).
% 1.94/0.62  fof(f35,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(rectify,[],[f34])).
% 1.94/0.62  fof(f34,plain,(
% 1.94/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(nnf_transformation,[],[f26])).
% 1.94/0.62  fof(f26,plain,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.94/0.62    inference(ennf_transformation,[],[f1])).
% 1.94/0.62  fof(f1,axiom,(
% 1.94/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.94/0.62  fof(f70,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) | ~v1_relat_1(X0) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2)) )),
% 1.94/0.62    inference(resolution,[],[f56,f51])).
% 1.94/0.62  fof(f51,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f37])).
% 1.94/0.62  fof(f56,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f29])).
% 1.94/0.62  fof(f29,plain,(
% 1.94/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 1.94/0.62    inference(flattening,[],[f28])).
% 1.94/0.62  fof(f28,plain,(
% 1.94/0.62    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.94/0.62    inference(ennf_transformation,[],[f13])).
% 1.94/0.62  fof(f13,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 1.94/0.62  fof(f1079,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | (spl4_8 | ~spl4_9)),
% 1.94/0.62    inference(resolution,[],[f1078,f57])).
% 1.94/0.62  fof(f57,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f31])).
% 1.94/0.62  fof(f31,plain,(
% 1.94/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.94/0.62    inference(flattening,[],[f30])).
% 1.94/0.62  fof(f30,plain,(
% 1.94/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.94/0.62    inference(ennf_transformation,[],[f2])).
% 1.94/0.62  fof(f2,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.94/0.62  fof(f1078,plain,(
% 1.94/0.62    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | (spl4_8 | ~spl4_9)),
% 1.94/0.62    inference(subsumption_resolution,[],[f1071,f196])).
% 1.94/0.62  fof(f196,plain,(
% 1.94/0.62    v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl4_9),
% 1.94/0.62    inference(avatar_component_clause,[],[f195])).
% 1.94/0.62  fof(f195,plain,(
% 1.94/0.62    spl4_9 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.94/0.62  fof(f1071,plain,(
% 1.94/0.62    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_8),
% 1.94/0.62    inference(resolution,[],[f1028,f106])).
% 1.94/0.62  fof(f106,plain,(
% 1.94/0.62    ( ! [X1] : (r1_tarski(k1_relat_1(X1),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(superposition,[],[f61,f60])).
% 1.94/0.62  fof(f60,plain,(
% 1.94/0.62    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f41,f59])).
% 1.94/0.62  fof(f59,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.94/0.62    inference(definition_unfolding,[],[f44,f58])).
% 1.94/0.62  fof(f58,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f45,f53])).
% 1.94/0.62  fof(f53,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f6])).
% 1.94/0.62  fof(f6,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.94/0.62  fof(f45,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f5])).
% 1.94/0.62  fof(f5,axiom,(
% 1.94/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.94/0.62  fof(f44,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f7])).
% 1.94/0.62  fof(f7,axiom,(
% 1.94/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.94/0.62  fof(f41,plain,(
% 1.94/0.62    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f19])).
% 1.94/0.62  fof(f19,plain,(
% 1.94/0.62    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.94/0.62    inference(ennf_transformation,[],[f8])).
% 1.94/0.62  fof(f8,axiom,(
% 1.94/0.62    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.94/0.62  fof(f61,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.94/0.62    inference(definition_unfolding,[],[f42,f59])).
% 1.94/0.62  fof(f42,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.94/0.62    inference(cnf_transformation,[],[f3])).
% 1.94/0.62  fof(f3,axiom,(
% 1.94/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.94/0.62  fof(f1028,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | spl4_8),
% 1.94/0.62    inference(resolution,[],[f193,f57])).
% 1.94/0.62  fof(f193,plain,(
% 1.94/0.62    ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl4_8),
% 1.94/0.62    inference(avatar_component_clause,[],[f191])).
% 1.94/0.62  fof(f191,plain,(
% 1.94/0.62    spl4_8 <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.94/0.62  fof(f1016,plain,(
% 1.94/0.62    ~spl4_9 | spl4_16),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f1015])).
% 1.94/0.62  fof(f1015,plain,(
% 1.94/0.62    $false | (~spl4_9 | spl4_16)),
% 1.94/0.62    inference(subsumption_resolution,[],[f1014,f39])).
% 1.94/0.62  fof(f1014,plain,(
% 1.94/0.62    ~r1_tarski(sK0,sK1) | (~spl4_9 | spl4_16)),
% 1.94/0.62    inference(subsumption_resolution,[],[f995,f38])).
% 1.94/0.62  fof(f995,plain,(
% 1.94/0.62    ~v1_relat_1(sK2) | ~r1_tarski(sK0,sK1) | (~spl4_9 | spl4_16)),
% 1.94/0.62    inference(resolution,[],[f387,f357])).
% 1.94/0.62  fof(f357,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | (~spl4_9 | spl4_16)),
% 1.94/0.62    inference(resolution,[],[f344,f57])).
% 1.94/0.62  fof(f344,plain,(
% 1.94/0.62    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_9 | spl4_16)),
% 1.94/0.62    inference(subsumption_resolution,[],[f338,f196])).
% 1.94/0.62  fof(f338,plain,(
% 1.94/0.62    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_16),
% 1.94/0.62    inference(resolution,[],[f288,f105])).
% 1.94/0.62  fof(f105,plain,(
% 1.94/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(superposition,[],[f72,f60])).
% 1.94/0.62  fof(f72,plain,(
% 1.94/0.62    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 1.94/0.62    inference(superposition,[],[f61,f62])).
% 1.94/0.62  fof(f62,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.94/0.62    inference(definition_unfolding,[],[f43,f58,f58])).
% 1.94/0.62  fof(f43,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f4])).
% 1.94/0.62  fof(f4,axiom,(
% 1.94/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.94/0.62  fof(f288,plain,(
% 1.94/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | spl4_16),
% 1.94/0.62    inference(resolution,[],[f276,f57])).
% 1.94/0.62  fof(f276,plain,(
% 1.94/0.62    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl4_16),
% 1.94/0.62    inference(avatar_component_clause,[],[f274])).
% 1.94/0.62  fof(f274,plain,(
% 1.94/0.62    spl4_16 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.94/0.62  fof(f281,plain,(
% 1.94/0.62    spl4_9),
% 1.94/0.62    inference(avatar_contradiction_clause,[],[f280])).
% 1.94/0.62  fof(f280,plain,(
% 1.94/0.62    $false | spl4_9),
% 1.94/0.62    inference(subsumption_resolution,[],[f278,f38])).
% 1.94/0.62  fof(f278,plain,(
% 1.94/0.62    ~v1_relat_1(sK2) | spl4_9),
% 1.94/0.62    inference(resolution,[],[f197,f46])).
% 1.94/0.62  fof(f46,plain,(
% 1.94/0.62    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f20])).
% 1.94/0.62  fof(f20,plain,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.94/0.62    inference(ennf_transformation,[],[f11])).
% 1.94/0.62  fof(f11,axiom,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.94/0.62  fof(f197,plain,(
% 1.94/0.62    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_9),
% 1.94/0.62    inference(avatar_component_clause,[],[f195])).
% 1.94/0.62  fof(f277,plain,(
% 1.94/0.62    ~spl4_9 | ~spl4_16 | spl4_10),
% 1.94/0.62    inference(avatar_split_clause,[],[f270,f199,f274,f195])).
% 1.94/0.62  fof(f199,plain,(
% 1.94/0.62    spl4_10 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 1.94/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.94/0.62  fof(f270,plain,(
% 1.94/0.62    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_10),
% 1.94/0.62    inference(trivial_inequality_removal,[],[f269])).
% 1.94/0.62  fof(f269,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_10),
% 1.94/0.62    inference(superposition,[],[f201,f48])).
% 1.94/0.62  fof(f48,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f23])).
% 1.94/0.62  fof(f23,plain,(
% 1.94/0.62    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(flattening,[],[f22])).
% 1.94/0.62  fof(f22,plain,(
% 1.94/0.62    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(ennf_transformation,[],[f9])).
% 1.94/0.62  fof(f9,axiom,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.94/0.62  fof(f201,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | spl4_10),
% 1.94/0.62    inference(avatar_component_clause,[],[f199])).
% 1.94/0.62  fof(f202,plain,(
% 1.94/0.62    ~spl4_8 | ~spl4_9 | ~spl4_10),
% 1.94/0.62    inference(avatar_split_clause,[],[f135,f199,f195,f191])).
% 1.94/0.62  fof(f135,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.94/0.62    inference(superposition,[],[f97,f69])).
% 1.94/0.62  fof(f69,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k8_relat_1(X1,X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 1.94/0.62    inference(duplicate_literal_removal,[],[f68])).
% 1.94/0.62  fof(f68,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k8_relat_1(X1,X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.94/0.62    inference(superposition,[],[f47,f49])).
% 1.94/0.62  fof(f49,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f25])).
% 1.94/0.62  fof(f25,plain,(
% 1.94/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(flattening,[],[f24])).
% 1.94/0.62  fof(f24,plain,(
% 1.94/0.62    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(ennf_transformation,[],[f10])).
% 1.94/0.62  fof(f10,axiom,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.94/0.62  fof(f47,plain,(
% 1.94/0.62    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f21])).
% 1.94/0.62  fof(f21,plain,(
% 1.94/0.62    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.94/0.62    inference(ennf_transformation,[],[f12])).
% 1.94/0.62  fof(f12,axiom,(
% 1.94/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 1.94/0.62  fof(f97,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.94/0.62    inference(subsumption_resolution,[],[f85,f38])).
% 1.94/0.62  fof(f85,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 1.94/0.62    inference(superposition,[],[f40,f54])).
% 1.94/0.62  fof(f54,plain,(
% 1.94/0.62    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 1.94/0.62    inference(cnf_transformation,[],[f27])).
% 1.94/0.62  fof(f27,plain,(
% 1.94/0.62    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.94/0.62    inference(ennf_transformation,[],[f14])).
% 1.94/0.62  fof(f14,axiom,(
% 1.94/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.94/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 1.94/0.62  fof(f40,plain,(
% 1.94/0.62    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.94/0.62    inference(cnf_transformation,[],[f33])).
% 1.94/0.62  % SZS output end Proof for theBenchmark
% 1.94/0.62  % (11309)------------------------------
% 1.94/0.62  % (11309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.62  % (11309)Termination reason: Refutation
% 1.94/0.62  
% 1.94/0.62  % (11309)Memory used [KB]: 6780
% 1.94/0.62  % (11309)Time elapsed: 0.198 s
% 1.94/0.62  % (11309)------------------------------
% 1.94/0.62  % (11309)------------------------------
% 2.03/0.62  % (11275)Success in time 0.269 s
%------------------------------------------------------------------------------
