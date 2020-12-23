%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 180 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  229 ( 549 expanded)
%              Number of equality atoms :   25 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f160,f248])).

fof(f248,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f243,f244])).

fof(f244,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),X0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f240,f82])).

fof(f82,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f81,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f81,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f49,f47])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),X0) )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f166,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f106,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f106,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f85,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f72,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f72,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))))
        | ~ r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f159,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f159,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_9
  <=> r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f243,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f159,f237])).

fof(f160,plain,
    ( spl5_9
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f104,f75,f65,f60,f55,f157])).

fof(f60,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,
    ( spl5_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( spl5_5
  <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f104,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(backward_demodulation,[],[f94,f102])).

fof(f102,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f57,f62,f67,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f45,f36,f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f67,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f62,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f94,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f78,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f73,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (801013760)
% 0.13/0.36  ipcrm: permission denied for id (802095105)
% 0.13/0.37  ipcrm: permission denied for id (802226181)
% 0.13/0.37  ipcrm: permission denied for id (805830662)
% 0.13/0.37  ipcrm: permission denied for id (802291719)
% 0.13/0.37  ipcrm: permission denied for id (802324488)
% 0.13/0.37  ipcrm: permission denied for id (802357257)
% 0.13/0.38  ipcrm: permission denied for id (801046539)
% 0.13/0.38  ipcrm: permission denied for id (802488334)
% 0.13/0.38  ipcrm: permission denied for id (805961743)
% 0.13/0.38  ipcrm: permission denied for id (802586641)
% 0.13/0.39  ipcrm: permission denied for id (806027282)
% 0.13/0.39  ipcrm: permission denied for id (806092820)
% 0.13/0.39  ipcrm: permission denied for id (806125589)
% 0.20/0.39  ipcrm: permission denied for id (806158358)
% 0.20/0.39  ipcrm: permission denied for id (802783255)
% 0.20/0.39  ipcrm: permission denied for id (806191128)
% 0.20/0.39  ipcrm: permission denied for id (802848793)
% 0.20/0.40  ipcrm: permission denied for id (802881562)
% 0.20/0.40  ipcrm: permission denied for id (802914331)
% 0.20/0.40  ipcrm: permission denied for id (802979869)
% 0.20/0.40  ipcrm: permission denied for id (801177630)
% 0.20/0.40  ipcrm: permission denied for id (803045408)
% 0.20/0.40  ipcrm: permission denied for id (803078177)
% 0.20/0.41  ipcrm: permission denied for id (803110946)
% 0.20/0.41  ipcrm: permission denied for id (806289443)
% 0.20/0.41  ipcrm: permission denied for id (803209252)
% 0.20/0.41  ipcrm: permission denied for id (803242021)
% 0.20/0.41  ipcrm: permission denied for id (803274790)
% 0.20/0.41  ipcrm: permission denied for id (803307559)
% 0.20/0.41  ipcrm: permission denied for id (803340328)
% 0.20/0.41  ipcrm: permission denied for id (806322217)
% 0.20/0.42  ipcrm: permission denied for id (803405866)
% 0.20/0.42  ipcrm: permission denied for id (803471404)
% 0.20/0.42  ipcrm: permission denied for id (803504173)
% 0.20/0.42  ipcrm: permission denied for id (803536942)
% 0.20/0.42  ipcrm: permission denied for id (803602480)
% 0.20/0.42  ipcrm: permission denied for id (806420529)
% 0.20/0.43  ipcrm: permission denied for id (801243186)
% 0.20/0.43  ipcrm: permission denied for id (803668019)
% 0.20/0.43  ipcrm: permission denied for id (801275956)
% 0.20/0.43  ipcrm: permission denied for id (806486070)
% 0.20/0.43  ipcrm: permission denied for id (803766327)
% 0.20/0.43  ipcrm: permission denied for id (806518840)
% 0.20/0.44  ipcrm: permission denied for id (803831865)
% 0.20/0.44  ipcrm: permission denied for id (803864634)
% 0.20/0.44  ipcrm: permission denied for id (803897403)
% 0.20/0.44  ipcrm: permission denied for id (806551612)
% 0.20/0.44  ipcrm: permission denied for id (804028479)
% 0.20/0.44  ipcrm: permission denied for id (804061248)
% 0.20/0.45  ipcrm: permission denied for id (801374273)
% 0.20/0.45  ipcrm: permission denied for id (801407042)
% 0.20/0.45  ipcrm: permission denied for id (801439812)
% 0.20/0.45  ipcrm: permission denied for id (804159557)
% 0.20/0.45  ipcrm: permission denied for id (801472582)
% 0.20/0.45  ipcrm: permission denied for id (806715463)
% 0.20/0.45  ipcrm: permission denied for id (804225096)
% 0.20/0.46  ipcrm: permission denied for id (806748233)
% 0.20/0.46  ipcrm: permission denied for id (804290634)
% 0.20/0.46  ipcrm: permission denied for id (806781003)
% 0.20/0.46  ipcrm: permission denied for id (801570892)
% 0.20/0.46  ipcrm: permission denied for id (804356173)
% 0.20/0.46  ipcrm: permission denied for id (804421711)
% 0.20/0.46  ipcrm: permission denied for id (804454480)
% 0.20/0.47  ipcrm: permission denied for id (804487249)
% 0.20/0.47  ipcrm: permission denied for id (804520018)
% 0.20/0.47  ipcrm: permission denied for id (804552787)
% 0.20/0.47  ipcrm: permission denied for id (804585556)
% 0.20/0.47  ipcrm: permission denied for id (801636437)
% 0.20/0.47  ipcrm: permission denied for id (804618326)
% 0.20/0.47  ipcrm: permission denied for id (801669207)
% 0.20/0.47  ipcrm: permission denied for id (804651096)
% 0.20/0.48  ipcrm: permission denied for id (804683865)
% 0.20/0.48  ipcrm: permission denied for id (804716634)
% 0.20/0.48  ipcrm: permission denied for id (801734748)
% 0.20/0.48  ipcrm: permission denied for id (804782173)
% 0.20/0.48  ipcrm: permission denied for id (801767518)
% 0.20/0.48  ipcrm: permission denied for id (804814943)
% 0.20/0.49  ipcrm: permission denied for id (804847712)
% 0.20/0.49  ipcrm: permission denied for id (804913250)
% 0.20/0.49  ipcrm: permission denied for id (804946019)
% 0.20/0.49  ipcrm: permission denied for id (801800293)
% 0.20/0.49  ipcrm: permission denied for id (805044327)
% 0.20/0.50  ipcrm: permission denied for id (801833064)
% 0.20/0.50  ipcrm: permission denied for id (805077097)
% 0.20/0.50  ipcrm: permission denied for id (807010411)
% 0.20/0.50  ipcrm: permission denied for id (807043180)
% 0.20/0.50  ipcrm: permission denied for id (805208173)
% 0.20/0.50  ipcrm: permission denied for id (805240942)
% 0.20/0.51  ipcrm: permission denied for id (805273711)
% 0.20/0.51  ipcrm: permission denied for id (801931377)
% 0.20/0.51  ipcrm: permission denied for id (805339250)
% 0.20/0.51  ipcrm: permission denied for id (807108723)
% 0.20/0.51  ipcrm: permission denied for id (801964148)
% 0.20/0.51  ipcrm: permission denied for id (801996918)
% 0.20/0.52  ipcrm: permission denied for id (807174263)
% 0.35/0.52  ipcrm: permission denied for id (807207032)
% 0.35/0.52  ipcrm: permission denied for id (805503097)
% 0.35/0.52  ipcrm: permission denied for id (805535866)
% 0.35/0.52  ipcrm: permission denied for id (805601404)
% 0.35/0.52  ipcrm: permission denied for id (805666942)
% 0.35/0.53  ipcrm: permission denied for id (805699711)
% 0.37/0.59  % (15012)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.37/0.61  % (15025)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.37/0.61  % (15025)Refutation found. Thanks to Tanya!
% 0.37/0.61  % SZS status Theorem for theBenchmark
% 0.37/0.61  % SZS output start Proof for theBenchmark
% 0.37/0.61  fof(f249,plain,(
% 0.37/0.61    $false),
% 0.37/0.61    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f160,f248])).
% 0.37/0.61  fof(f248,plain,(
% 0.37/0.61    ~spl5_1 | ~spl5_4 | ~spl5_9),
% 0.37/0.61    inference(avatar_contradiction_clause,[],[f247])).
% 0.37/0.61  fof(f247,plain,(
% 0.37/0.61    $false | (~spl5_1 | ~spl5_4 | ~spl5_9)),
% 0.37/0.61    inference(subsumption_resolution,[],[f243,f244])).
% 0.37/0.61  fof(f244,plain,(
% 0.37/0.61    ( ! [X0] : (~r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),X0)) ) | (~spl5_1 | ~spl5_4 | ~spl5_9)),
% 0.37/0.61    inference(subsumption_resolution,[],[f240,f82])).
% 0.37/0.61  fof(f82,plain,(
% 0.37/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.37/0.61    inference(forward_demodulation,[],[f81,f53])).
% 0.37/0.61  fof(f53,plain,(
% 0.37/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.37/0.61    inference(forward_demodulation,[],[f48,f47])).
% 0.37/0.61  fof(f47,plain,(
% 0.37/0.61    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.37/0.61    inference(definition_unfolding,[],[f33,f36])).
% 0.37/0.61  fof(f36,plain,(
% 0.37/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.37/0.61    inference(cnf_transformation,[],[f7])).
% 0.37/0.61  fof(f7,axiom,(
% 0.37/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.37/0.61  fof(f33,plain,(
% 0.37/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f4])).
% 0.37/0.61  fof(f4,axiom,(
% 0.37/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.37/0.61  fof(f48,plain,(
% 0.37/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 0.37/0.61    inference(definition_unfolding,[],[f34,f46])).
% 0.37/0.61  fof(f46,plain,(
% 0.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.37/0.61    inference(definition_unfolding,[],[f37,f36])).
% 0.37/0.61  fof(f37,plain,(
% 0.37/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.37/0.61    inference(cnf_transformation,[],[f3])).
% 0.37/0.61  fof(f3,axiom,(
% 0.37/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.37/0.61  fof(f34,plain,(
% 0.37/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.37/0.61    inference(cnf_transformation,[],[f5])).
% 0.37/0.61  fof(f5,axiom,(
% 0.37/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.37/0.61  fof(f81,plain,(
% 0.37/0.61    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.37/0.61    inference(superposition,[],[f49,f47])).
% 0.37/0.61  fof(f49,plain,(
% 0.37/0.61    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1)) )),
% 0.37/0.61    inference(definition_unfolding,[],[f35,f46])).
% 0.37/0.61  fof(f35,plain,(
% 0.37/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f6])).
% 0.37/0.61  fof(f6,axiom,(
% 0.37/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.37/0.61  fof(f240,plain,(
% 0.37/0.61    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),X0)) ) | (~spl5_1 | ~spl5_4 | ~spl5_9)),
% 0.37/0.61    inference(backward_demodulation,[],[f166,f237])).
% 0.37/0.61  fof(f237,plain,(
% 0.37/0.61    k1_xboole_0 = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) | (~spl5_1 | ~spl5_4)),
% 0.37/0.61    inference(unit_resulting_resolution,[],[f106,f93])).
% 0.37/0.61  fof(f93,plain,(
% 0.37/0.61    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) ) | ~spl5_1),
% 0.37/0.61    inference(resolution,[],[f44,f57])).
% 0.37/0.61  fof(f57,plain,(
% 0.37/0.61    v1_relat_1(sK2) | ~spl5_1),
% 0.37/0.61    inference(avatar_component_clause,[],[f55])).
% 0.37/0.61  fof(f55,plain,(
% 0.37/0.61    spl5_1 <=> v1_relat_1(sK2)),
% 0.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.37/0.61  fof(f44,plain,(
% 0.37/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f27])).
% 0.37/0.61  fof(f27,plain,(
% 0.37/0.61    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.37/0.61    inference(nnf_transformation,[],[f18])).
% 0.37/0.61  fof(f18,plain,(
% 0.37/0.61    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.37/0.61    inference(ennf_transformation,[],[f8])).
% 0.37/0.61  fof(f8,axiom,(
% 0.37/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.37/0.61  fof(f106,plain,(
% 0.37/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_setfam_1(k2_tarski(sK0,sK1)))) ) | ~spl5_4),
% 0.37/0.61    inference(unit_resulting_resolution,[],[f85,f41])).
% 0.37/0.61  fof(f41,plain,(
% 0.37/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f26])).
% 0.37/0.61  fof(f26,plain,(
% 0.37/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.37/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f25])).
% 0.37/0.61  fof(f25,plain,(
% 0.37/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.37/0.61    introduced(choice_axiom,[])).
% 0.37/0.61  fof(f17,plain,(
% 0.37/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.37/0.61    inference(ennf_transformation,[],[f13])).
% 0.37/0.61  fof(f13,plain,(
% 0.37/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.61    inference(rectify,[],[f1])).
% 0.37/0.61  fof(f1,axiom,(
% 0.37/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.37/0.61  fof(f85,plain,(
% 0.37/0.61    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(sK0,sK1)))) ) | ~spl5_4),
% 0.37/0.61    inference(unit_resulting_resolution,[],[f72,f50])).
% 0.37/0.61  fof(f50,plain,(
% 0.37/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.37/0.61    inference(definition_unfolding,[],[f39,f36])).
% 0.37/0.61  fof(f39,plain,(
% 0.37/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.37/0.61    inference(cnf_transformation,[],[f24])).
% 0.37/0.61  fof(f24,plain,(
% 0.37/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.37/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).
% 0.37/0.61  fof(f23,plain,(
% 0.37/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.37/0.61    introduced(choice_axiom,[])).
% 0.37/0.61  fof(f16,plain,(
% 0.37/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.37/0.61    inference(ennf_transformation,[],[f12])).
% 0.37/0.61  fof(f12,plain,(
% 0.37/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.61    inference(rectify,[],[f2])).
% 0.37/0.61  fof(f2,axiom,(
% 0.37/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.37/0.61  fof(f72,plain,(
% 0.37/0.61    r1_xboole_0(sK0,sK1) | ~spl5_4),
% 0.37/0.61    inference(avatar_component_clause,[],[f70])).
% 0.37/0.61  fof(f70,plain,(
% 0.37/0.61    spl5_4 <=> r1_xboole_0(sK0,sK1)),
% 0.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.37/0.61  fof(f166,plain,(
% 0.37/0.61    ( ! [X0] : (~r1_xboole_0(X0,k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))) | ~r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),X0)) ) | ~spl5_9),
% 0.37/0.61    inference(resolution,[],[f159,f42])).
% 0.37/0.61  fof(f42,plain,(
% 0.37/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f26])).
% 0.37/0.61  fof(f159,plain,(
% 0.37/0.61    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))) | ~spl5_9),
% 0.37/0.61    inference(avatar_component_clause,[],[f157])).
% 0.37/0.61  fof(f157,plain,(
% 0.37/0.61    spl5_9 <=> r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))))),
% 0.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.37/0.61  fof(f243,plain,(
% 0.37/0.61    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k1_xboole_0) | (~spl5_1 | ~spl5_4 | ~spl5_9)),
% 0.37/0.61    inference(backward_demodulation,[],[f159,f237])).
% 0.37/0.61  fof(f160,plain,(
% 0.37/0.61    spl5_9 | ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5),
% 0.37/0.61    inference(avatar_split_clause,[],[f104,f75,f65,f60,f55,f157])).
% 0.37/0.61  fof(f60,plain,(
% 0.37/0.61    spl5_2 <=> v1_funct_1(sK2)),
% 0.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.37/0.61  fof(f65,plain,(
% 0.37/0.61    spl5_3 <=> v2_funct_1(sK2)),
% 0.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.37/0.61  fof(f75,plain,(
% 0.37/0.61    spl5_5 <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.37/0.61  fof(f104,plain,(
% 0.37/0.61    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5)),
% 0.37/0.61    inference(backward_demodulation,[],[f94,f102])).
% 0.37/0.61  fof(f102,plain,(
% 0.37/0.61    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.37/0.61    inference(unit_resulting_resolution,[],[f57,f62,f67,f52])).
% 0.37/0.61  fof(f52,plain,(
% 0.37/0.61    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.37/0.61    inference(definition_unfolding,[],[f45,f36,f36])).
% 0.37/0.61  fof(f45,plain,(
% 0.37/0.61    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f20])).
% 0.37/0.61  fof(f20,plain,(
% 0.37/0.61    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/0.61    inference(flattening,[],[f19])).
% 0.37/0.61  fof(f19,plain,(
% 0.37/0.61    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.37/0.61    inference(ennf_transformation,[],[f9])).
% 0.37/0.61  fof(f9,axiom,(
% 0.37/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.37/0.61  fof(f67,plain,(
% 0.37/0.61    v2_funct_1(sK2) | ~spl5_3),
% 0.37/0.61    inference(avatar_component_clause,[],[f65])).
% 0.37/0.61  fof(f62,plain,(
% 0.37/0.61    v1_funct_1(sK2) | ~spl5_2),
% 0.37/0.61    inference(avatar_component_clause,[],[f60])).
% 0.37/0.61  fof(f94,plain,(
% 0.37/0.61    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | spl5_5),
% 0.37/0.61    inference(unit_resulting_resolution,[],[f77,f51])).
% 0.37/0.61  fof(f51,plain,(
% 0.37/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.37/0.61    inference(definition_unfolding,[],[f38,f36])).
% 0.37/0.61  fof(f38,plain,(
% 0.37/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.37/0.61    inference(cnf_transformation,[],[f24])).
% 0.37/0.61  fof(f77,plain,(
% 0.37/0.61    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl5_5),
% 0.37/0.61    inference(avatar_component_clause,[],[f75])).
% 0.37/0.61  fof(f78,plain,(
% 0.37/0.61    ~spl5_5),
% 0.37/0.61    inference(avatar_split_clause,[],[f32,f75])).
% 0.37/0.61  fof(f32,plain,(
% 0.37/0.61    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.37/0.61    inference(cnf_transformation,[],[f22])).
% 0.37/0.61  fof(f22,plain,(
% 0.37/0.61    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.37/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21])).
% 0.37/0.61  fof(f21,plain,(
% 0.37/0.61    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.37/0.61    introduced(choice_axiom,[])).
% 0.37/0.61  fof(f15,plain,(
% 0.37/0.61    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.37/0.61    inference(flattening,[],[f14])).
% 0.37/0.61  fof(f14,plain,(
% 0.37/0.61    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.37/0.61    inference(ennf_transformation,[],[f11])).
% 0.37/0.61  fof(f11,negated_conjecture,(
% 0.37/0.61    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.37/0.61    inference(negated_conjecture,[],[f10])).
% 0.37/0.61  fof(f10,conjecture,(
% 0.37/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.37/0.61  fof(f73,plain,(
% 0.37/0.61    spl5_4),
% 0.37/0.61    inference(avatar_split_clause,[],[f30,f70])).
% 0.37/0.61  fof(f30,plain,(
% 0.37/0.61    r1_xboole_0(sK0,sK1)),
% 0.37/0.61    inference(cnf_transformation,[],[f22])).
% 0.37/0.61  fof(f68,plain,(
% 0.37/0.61    spl5_3),
% 0.37/0.61    inference(avatar_split_clause,[],[f31,f65])).
% 0.37/0.61  fof(f31,plain,(
% 0.37/0.61    v2_funct_1(sK2)),
% 0.37/0.61    inference(cnf_transformation,[],[f22])).
% 0.37/0.61  fof(f63,plain,(
% 0.37/0.61    spl5_2),
% 0.37/0.61    inference(avatar_split_clause,[],[f29,f60])).
% 0.37/0.61  fof(f29,plain,(
% 0.37/0.61    v1_funct_1(sK2)),
% 0.37/0.61    inference(cnf_transformation,[],[f22])).
% 0.37/0.61  fof(f58,plain,(
% 0.37/0.61    spl5_1),
% 0.37/0.61    inference(avatar_split_clause,[],[f28,f55])).
% 0.37/0.61  fof(f28,plain,(
% 0.37/0.61    v1_relat_1(sK2)),
% 0.37/0.61    inference(cnf_transformation,[],[f22])).
% 0.37/0.61  % SZS output end Proof for theBenchmark
% 0.37/0.61  % (15025)------------------------------
% 0.37/0.61  % (15025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.61  % (15025)Termination reason: Refutation
% 0.37/0.61  
% 0.37/0.61  % (15025)Memory used [KB]: 10746
% 0.37/0.61  % (15025)Time elapsed: 0.038 s
% 0.37/0.61  % (15025)------------------------------
% 0.37/0.61  % (15025)------------------------------
% 0.37/0.63  % (15015)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.37/0.63  % (15011)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.37/0.64  % (14853)Success in time 0.278 s
%------------------------------------------------------------------------------
