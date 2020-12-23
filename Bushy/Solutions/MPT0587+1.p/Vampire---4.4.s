%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t191_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:56 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  83 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f62,f74,f92])).

fof(f92,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f83,f36])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t191_relat_1.p',idempotence_k3_xboole_0)).

fof(f83,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)),sK0)
    | ~ spl3_5 ),
    inference(superposition,[],[f73,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k6_subset_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k6_subset_1(X1,X2)) ),
    inference(forward_demodulation,[],[f47,f39])).

fof(f39,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t191_relat_1.p',redefinition_k6_subset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k6_subset_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f42,f39])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t191_relat_1.p',t49_xboole_1)).

fof(f73,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k3_xboole_0(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_5
  <=> k6_subset_1(k1_relat_1(sK1),sK0) != k3_xboole_0(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f74,plain,
    ( ~ spl3_5
    | ~ spl3_0
    | spl3_3 ),
    inference(avatar_split_clause,[],[f67,f60,f53,f72])).

fof(f53,plain,
    ( spl3_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f60,plain,
    ( spl3_3
  <=> k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f67,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k3_xboole_0(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ spl3_0
    | ~ spl3_3 ),
    inference(superposition,[],[f61,f65])).

fof(f65,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl3_0 ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f53])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t191_relat_1.p',t90_relat_1)).

fof(f61,plain,
    ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) != k6_subset_1(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) != k6_subset_1(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t191_relat_1.p',t191_relat_1)).

fof(f55,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
