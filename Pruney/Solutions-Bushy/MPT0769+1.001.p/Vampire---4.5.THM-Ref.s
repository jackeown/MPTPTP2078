%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0769+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  61 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   89 ( 135 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f36,f41,f48,f51])).

fof(f51,plain,
    ( spl2_1
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl2_1
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)
    | spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f17,f46])).

fof(f46,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_7
  <=> ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f17,plain,
    ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl2_1
  <=> k2_wellord1(sK1,sK0) = k8_relat_1(sK0,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,
    ( spl2_7
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f43,f39,f34,f45])).

fof(f34,plain,
    ( spl2_5
  <=> ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f39,plain,
    ( spl2_6
  <=> ! [X1,X0] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k8_relat_1(X0,k7_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f43,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k8_relat_1(X0,k7_relat_1(sK1,X1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f35,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f41,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f37,f29,f20,f39])).

fof(f20,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f29,plain,
    ( spl2_4
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f37,plain,
    ( ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k8_relat_1(X0,k7_relat_1(sK1,X1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f30,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f36,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f32,f25,f20,f34])).

fof(f25,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f32,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f26,f22])).

fof(f26,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f31,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f27,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f23,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f18,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
