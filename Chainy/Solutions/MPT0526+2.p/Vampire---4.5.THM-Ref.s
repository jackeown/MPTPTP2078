%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0526+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  81 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1016,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f899,f903,f981,f1015])).

fof(f1015,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f1014])).

fof(f1014,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1011,f898])).

fof(f898,plain,
    ( sK0 != k8_relat_1(k2_relat_1(sK0),sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl8_1
  <=> sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1011,plain,
    ( sK0 = k8_relat_1(k2_relat_1(sK0),sK0)
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(superposition,[],[f980,f995])).

fof(f995,plain,
    ( ! [X0] : k8_relat_1(X0,sK0) = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),X0))
    | ~ spl8_2 ),
    inference(resolution,[],[f853,f902])).

fof(f902,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f901])).

fof(f901,plain,
    ( spl8_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f853,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f785])).

fof(f785,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f700,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f980,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f979])).

fof(f979,plain,
    ( spl8_8
  <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f981,plain,
    ( spl8_8
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f975,f901,f979])).

fof(f975,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl8_2 ),
    inference(resolution,[],[f882,f902])).

fof(f882,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f812])).

fof(f812,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f711])).

fof(f711,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f903,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f836,f901])).

fof(f836,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f817])).

fof(f817,plain,
    ( sK0 != k8_relat_1(k2_relat_1(sK0),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f774,f816])).

fof(f816,plain,
    ( ? [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k8_relat_1(k2_relat_1(sK0),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f774,plain,(
    ? [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f703])).

fof(f703,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(negated_conjecture,[],[f702])).

fof(f702,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f899,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f837,f897])).

fof(f837,plain,(
    sK0 != k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(cnf_transformation,[],[f817])).
%------------------------------------------------------------------------------
