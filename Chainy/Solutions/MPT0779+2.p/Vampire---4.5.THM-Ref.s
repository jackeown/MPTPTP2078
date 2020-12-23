%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0779+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  63 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3122,f3132,f3251])).

fof(f3251,plain,
    ( ~ spl150_1
    | spl150_3 ),
    inference(avatar_contradiction_clause,[],[f3250])).

fof(f3250,plain,
    ( $false
    | ~ spl150_1
    | spl150_3 ),
    inference(trivial_inequality_removal,[],[f3249])).

fof(f3249,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)
    | ~ spl150_1
    | spl150_3 ),
    inference(forward_demodulation,[],[f3243,f2130])).

fof(f2130,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f1168])).

fof(f1168,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f3243,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0))
    | ~ spl150_1
    | spl150_3 ),
    inference(superposition,[],[f3131,f3180])).

fof(f3180,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))
    | ~ spl150_1 ),
    inference(unit_resulting_resolution,[],[f3121,f2063])).

fof(f2063,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1179])).

fof(f1179,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1160])).

fof(f1160,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f3121,plain,
    ( v1_relat_1(sK1)
    | ~ spl150_1 ),
    inference(avatar_component_clause,[],[f3119])).

fof(f3119,plain,
    ( spl150_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl150_1])])).

fof(f3131,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    | spl150_3 ),
    inference(avatar_component_clause,[],[f3129])).

fof(f3129,plain,
    ( spl150_3
  <=> k2_wellord1(sK1,sK0) = k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl150_3])])).

fof(f3132,plain,(
    ~ spl150_3 ),
    inference(avatar_split_clause,[],[f2059,f3129])).

fof(f2059,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f1732])).

fof(f1732,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1175,f1731])).

fof(f1731,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1175,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1163])).

fof(f1163,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f1162])).

fof(f1162,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

fof(f3122,plain,(
    spl150_1 ),
    inference(avatar_split_clause,[],[f2058,f3119])).

fof(f2058,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1732])).
%------------------------------------------------------------------------------
