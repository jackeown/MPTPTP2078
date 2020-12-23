%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t40_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 112 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 293 expanded)
%              Number of equality atoms :   19 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f66,f85,f96,f129,f131,f133,f135])).

fof(f135,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK1,X0),k3_relat_1(sK1))
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t40_wellord1.p',t13_wellord1)).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f124,plain,
    ( ~ r1_tarski(k1_wellord1(sK1,sK0),k3_relat_1(sK1))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f58,f65,f84,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t40_wellord1.p',t39_wellord1)).

fof(f84,plain,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_5
  <=> k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f65,plain,
    ( v2_wellord1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> v2_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f133,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f125,f65])).

fof(f125,plain,
    ( ~ v2_wellord1(sK1)
    | ~ spl3_0
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f58,f72,f84,f50])).

fof(f131,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f126,f58])).

fof(f126,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f65,f72,f84,f50])).

fof(f129,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f58,f65,f72,f84,f50])).

fof(f96,plain,
    ( spl3_6
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f86,f57,f94])).

fof(f94,plain,
    ( spl3_6
  <=> k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f86,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t40_wellord1.p',d6_relat_1)).

fof(f85,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t40_wellord1.p',t40_wellord1)).

fof(f66,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f38,f57])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
