%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t211_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:59 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  56 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 145 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f49,f59,f68,f89])).

fof(f89,plain,
    ( ~ spl4_0
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f58,f72])).

fof(f72,plain,
    ( ! [X0] : k7_relat_1(sK2,k6_subset_1(sK0,X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(superposition,[],[f70,f67])).

fof(f67,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_6
  <=> k7_relat_1(sK2,sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f70,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))
    | ~ spl4_0 ),
    inference(resolution,[],[f35,f41])).

fof(f41,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t211_relat_1.p',t109_relat_1)).

fof(f58,plain,
    ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_5
  <=> k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_6
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f47,f40,f66])).

fof(f47,plain,
    ( spl4_2
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f61,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f60,f41])).

fof(f60,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t211_relat_1.p',t97_relat_1)).

fof(f59,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1))
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1))
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k1_relat_1(X2),X0)
         => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t211_relat_1.p',t211_relat_1)).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f25,f40])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
