%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 176 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  308 ( 572 expanded)
%              Number of equality atoms :   74 ( 138 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f69,f79,f88,f95,f113,f134,f141,f171,f177,f198])).

fof(f198,plain,
    ( ~ spl1_1
    | spl1_7
    | ~ spl1_20 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl1_1
    | spl1_7
    | ~ spl1_20 ),
    inference(subsumption_resolution,[],[f196,f83])).

fof(f83,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl1_7
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f196,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_1
    | ~ spl1_20 ),
    inference(subsumption_resolution,[],[f192,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f192,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_1
    | ~ spl1_20 ),
    inference(resolution,[],[f170,f42])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) )
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl1_20
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f177,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | spl1_19 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_2
    | spl1_19 ),
    inference(subsumption_resolution,[],[f175,f42])).

fof(f175,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_2
    | spl1_19 ),
    inference(subsumption_resolution,[],[f173,f47])).

fof(f47,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f173,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_19 ),
    inference(resolution,[],[f167,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f167,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl1_19
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f171,plain,
    ( ~ spl1_19
    | spl1_20
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f90,f66,f169,f165])).

fof(f66,plain,
    ( spl1_5
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_5 ),
    inference(superposition,[],[f29,f68])).

fof(f68,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f141,plain,
    ( spl1_8
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f139,f132,f110,f45,f40,f85])).

fof(f85,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f110,plain,
    ( spl1_11
  <=> k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f132,plain,
    ( spl1_14
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f139,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f138,f112])).

fof(f112,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f138,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(subsumption_resolution,[],[f136,f42])).

fof(f136,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(resolution,[],[f133,f47])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl1_14
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f97,f93,f132])).

fof(f93,plain,
    ( spl1_9
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f97,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_9 ),
    inference(resolution,[],[f94,f30])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0)) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f113,plain,
    ( spl1_11
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f107,f76,f66,f45,f40,f110])).

fof(f76,plain,
    ( spl1_6
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f107,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f106,f78])).

fof(f78,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f106,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f105,f68])).

fof(f105,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | ~ spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f103,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f30])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f95,plain,
    ( spl1_9
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f73,f40,f93])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0)) )
    | ~ spl1_1 ),
    inference(resolution,[],[f28,f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f88,plain,
    ( ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f26,f85,f81])).

fof(f26,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f79,plain,
    ( spl1_6
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f72,f50,f45,f40,f76])).

fof(f50,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f72,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f71,f42])).

fof(f71,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f70,f47])).

fof(f70,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f69,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f64,f50,f45,f40,f66])).

fof(f64,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f63,f42])).

fof(f63,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f62,f47])).

fof(f62,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f32,f52])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (31790)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (31771)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (31766)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (31772)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (31768)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (31768)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f43,f48,f53,f69,f79,f88,f95,f113,f134,f141,f171,f177,f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ~spl1_1 | spl1_7 | ~spl1_20),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    $false | (~spl1_1 | spl1_7 | ~spl1_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f196,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl1_7 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl1_1 | ~spl1_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f192,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl1_1 | ~spl1_20)),
% 0.20/0.51    inference(resolution,[],[f170,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    v1_relat_1(sK0) | ~spl1_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl1_1 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))) ) | ~spl1_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl1_20 <=> ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ~spl1_1 | ~spl1_2 | spl1_19),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f176])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    $false | (~spl1_1 | ~spl1_2 | spl1_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f175,f42])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | (~spl1_2 | spl1_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f173,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v1_funct_1(sK0) | ~spl1_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl1_2 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_19),
% 0.20/0.51    inference(resolution,[],[f167,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ~v1_relat_1(k2_funct_1(sK0)) | spl1_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f165])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    spl1_19 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ~spl1_19 | spl1_20 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f90,f66,f169,f165])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl1_5 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | ~spl1_5),
% 0.20/0.51    inference(superposition,[],[f29,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    spl1_8 | ~spl1_1 | ~spl1_2 | ~spl1_11 | ~spl1_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f139,f132,f110,f45,f40,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl1_8 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl1_11 <=> k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    spl1_14 <=> ! [X0] : (k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl1_1 | ~spl1_2 | ~spl1_11 | ~spl1_14)),
% 0.20/0.51    inference(forward_demodulation,[],[f138,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | ~spl1_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (~spl1_1 | ~spl1_2 | ~spl1_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f136,f42])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_14)),
% 0.20/0.51    inference(resolution,[],[f133,f47])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0)) ) | ~spl1_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f132])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl1_14 | ~spl1_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f97,f93,f132])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl1_9 <=> ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_9),
% 0.20/0.51    inference(resolution,[],[f94,f30])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0))) ) | ~spl1_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl1_11 | ~spl1_1 | ~spl1_2 | ~spl1_5 | ~spl1_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f107,f76,f66,f45,f40,f110])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl1_6 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (~spl1_1 | ~spl1_2 | ~spl1_5 | ~spl1_6)),
% 0.20/0.51    inference(forward_demodulation,[],[f106,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f76])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (~spl1_1 | ~spl1_2 | ~spl1_5)),
% 0.20/0.51    inference(forward_demodulation,[],[f105,f68])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) | (~spl1_1 | ~spl1_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f42])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(sK0) | ~spl1_2),
% 0.20/0.51    inference(resolution,[],[f55,f47])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f27,f30])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl1_9 | ~spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f40,f93])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0))) ) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f28,f42])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ~spl1_7 | ~spl1_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f85,f81])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl1_6 | ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f72,f50,f45,f40,f76])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl1_3 <=> v2_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | (~spl1_1 | ~spl1_2 | ~spl1_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f71,f42])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f47])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.51    inference(resolution,[],[f33,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v2_funct_1(sK0) | ~spl1_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl1_5 | ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f64,f50,f45,f40,f66])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_1 | ~spl1_2 | ~spl1_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f63,f42])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f62,f47])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.51    inference(resolution,[],[f32,f52])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f50])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    v2_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    spl1_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f45])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f40])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (31768)------------------------------
% 0.20/0.51  % (31768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31768)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (31768)Memory used [KB]: 6268
% 0.20/0.51  % (31768)Time elapsed: 0.096 s
% 0.20/0.51  % (31768)------------------------------
% 0.20/0.51  % (31768)------------------------------
% 0.20/0.51  % (31789)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (31780)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (31774)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (31784)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (31776)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (31775)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (31779)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (31765)Success in time 0.157 s
%------------------------------------------------------------------------------
