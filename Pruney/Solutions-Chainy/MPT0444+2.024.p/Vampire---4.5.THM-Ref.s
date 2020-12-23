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
% DateTime   : Thu Dec  3 12:47:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 ( 461 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f141,f147,f151,f159])).

fof(f159,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f157,f148])).

fof(f148,plain,
    ( sP1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_3 ),
    inference(resolution,[],[f135,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
          | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> sP0(X1,X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f135,plain,
    ( v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_3
  <=> v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f157,plain,
    ( ~ sP1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f156,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)
      | ~ sP1(k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(resolution,[],[f76,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X0)))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f76,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | r1_tarski(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ~ sP0(X1,X0) )
          & ( sP0(X1,X0)
            | ~ r1_tarski(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X0] : sP0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP0(X0,X0)
      | sP0(X0,X0) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(k4_tarski(X2,X3),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X3),X0) ) )
      & ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK3)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f155,f135])).

fof(f155,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_2 ),
    inference(subsumption_resolution,[],[f154,f31])).

fof(f31,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f154,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_2 ),
    inference(resolution,[],[f129,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f129,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK3))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_2
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f151,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f149,f148])).

fof(f149,plain,
    ( ~ sP1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_4 ),
    inference(resolution,[],[f140,f79])).

fof(f79,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X3,X4)),X3)
      | ~ sP1(k1_setfam_1(k2_tarski(X3,X4))) ) ),
    inference(resolution,[],[f76,f50])).

fof(f140,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_4
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f147,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f143,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f143,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_3 ),
    inference(resolution,[],[f136,f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(X2,X3)))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f136,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f141,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f132,f123,f138,f134])).

fof(f123,plain,
    ( spl6_1
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f132,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f131,f30])).

fof(f131,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_1 ),
    inference(resolution,[],[f125,f34])).

fof(f125,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f96,f127,f123])).

fof(f96,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK2)) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k1_setfam_1(k2_tarski(k2_relat_1(sK2),k2_relat_1(sK3)))) ),
    inference(definition_unfolding,[],[f32,f42,f42])).

fof(f32,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22645)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (22655)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (22659)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (22662)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (22649)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (22651)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (22647)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (22654)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (22650)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (22652)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (22654)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f130,f141,f147,f151,f159])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl6_2 | ~spl6_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    $false | (spl6_2 | ~spl6_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f157,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    sP1(k1_setfam_1(k2_tarski(sK2,sK3))) | ~spl6_3),
% 0.22/0.49    inference(resolution,[],[f135,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | sP1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(definition_folding,[],[f14,f20,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> sP0(X1,X0)) | ~sP1(X0))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl6_3 <=> v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ~sP1(k1_setfam_1(k2_tarski(sK2,sK3))) | (spl6_2 | ~spl6_3)),
% 0.22/0.49    inference(resolution,[],[f156,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) | ~sP1(k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.22/0.49    inference(resolution,[],[f76,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X0))) | r1_tarski(X2,X0)) )),
% 0.22/0.49    inference(superposition,[],[f50,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f41,f42,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f45,f42])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,X0) | ~sP1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f75,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP0(X1,X0) | r1_tarski(X0,X1) | ~sP1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_tarski(X0,X1))) | ~sP1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0] : (sP0(X0,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0] : (sP0(X0,X0) | sP0(X0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f39,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X2,X3),X1)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X2,X3),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~sP0(X1,X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f19])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK3) | (spl6_2 | ~spl6_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f155,f135])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK3) | ~v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f154,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))) & v1_relat_1(sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_2),
% 0.22/0.49    inference(resolution,[],[f129,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK3)) | spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl6_2 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ~spl6_3 | spl6_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f150])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    $false | (~spl6_3 | spl6_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f149,f148])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ~sP1(k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_4),
% 0.22/0.49    inference(resolution,[],[f140,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k2_tarski(X3,X4)),X3) | ~sP1(k1_setfam_1(k2_tarski(X3,X4)))) )),
% 0.22/0.49    inference(resolution,[],[f76,f50])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2) | spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl6_4 <=> r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl6_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    $false | spl6_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f143,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl6_3),
% 0.22/0.49    inference(resolution,[],[f136,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X3] : (v1_relat_1(k1_setfam_1(k2_tarski(X2,X3))) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(superposition,[],[f44,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f43,f42])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~spl6_3 | ~spl6_4 | spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f123,f138,f134])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl6_1 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2) | ~v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f131,f30])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_1),
% 0.22/0.49    inference(resolution,[],[f125,f34])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK2)) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f123])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ~spl6_1 | ~spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f127,f123])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK3)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k2_relat_1(sK2))),
% 0.22/0.49    inference(resolution,[],[f51,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_tarski(sK2,sK3))),k1_setfam_1(k2_tarski(k2_relat_1(sK2),k2_relat_1(sK3))))),
% 0.22/0.49    inference(definition_unfolding,[],[f32,f42,f42])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)))),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f46,f42])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (22654)------------------------------
% 0.22/0.49  % (22654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22654)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (22654)Memory used [KB]: 10746
% 0.22/0.49  % (22654)Time elapsed: 0.074 s
% 0.22/0.49  % (22654)------------------------------
% 0.22/0.49  % (22654)------------------------------
% 0.22/0.50  % (22636)Success in time 0.133 s
%------------------------------------------------------------------------------
