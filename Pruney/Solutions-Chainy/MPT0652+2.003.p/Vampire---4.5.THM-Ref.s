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
% DateTime   : Thu Dec  3 12:52:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 186 expanded)
%              Number of leaves         :   24 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  320 ( 560 expanded)
%              Number of equality atoms :   91 ( 165 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f65,f73,f83,f91,f102,f108,f114,f148,f231,f237,f278,f291])).

fof(f291,plain,
    ( ~ spl1_1
    | spl1_9
    | ~ spl1_29 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl1_1
    | spl1_9
    | ~ spl1_29 ),
    inference(subsumption_resolution,[],[f289,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f289,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_1
    | spl1_9
    | ~ spl1_29 ),
    inference(subsumption_resolution,[],[f285,f101])).

fof(f101,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f99])).

% (18333)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f99,plain,
    ( spl1_9
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f285,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_29 ),
    inference(resolution,[],[f277,f47])).

fof(f47,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) )
    | ~ spl1_29 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl1_29
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
        | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_29])])).

fof(f278,plain,
    ( spl1_29
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f166,f70,f62,f45,f276])).

fof(f62,plain,
    ( spl1_4
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f70,plain,
    ( spl1_5
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
        | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f165,f72])).

fof(f72,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f165,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(X0)) )
    | ~ spl1_1
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f163,f64])).

fof(f64,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(X0)) )
    | ~ spl1_1 ),
    inference(resolution,[],[f104,f47])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k1_relat_1(k4_relat_1(X1)) = k1_relat_1(k5_relat_1(k4_relat_1(X1),X2))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(X1)),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f237,plain,
    ( ~ spl1_1
    | spl1_8
    | ~ spl1_16
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl1_1
    | spl1_8
    | ~ spl1_16
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f235,f97])).

fof(f97,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl1_8
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f235,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_1
    | ~ spl1_16
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f232,f147])).

fof(f147,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl1_16
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f232,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_24 ),
    inference(resolution,[],[f230,f47])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0)) )
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl1_24
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f231,plain,
    ( spl1_24
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f162,f70,f45,f229])).

fof(f162,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_1
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f160,f72])).

fof(f160,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k2_relat_1(k4_relat_1(sK0)))
        | ~ v1_relat_1(X0) )
    | ~ spl1_1 ),
    inference(resolution,[],[f87,f47])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k5_relat_1(k4_relat_1(X2),X1)) = k9_relat_1(X1,k2_relat_1(k4_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f148,plain,
    ( spl1_16
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f118,f111,f89,f145])).

fof(f89,plain,
    ( spl1_7
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f111,plain,
    ( spl1_11
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f118,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(superposition,[],[f90,f113])).

fof(f113,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f90,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f114,plain,
    ( spl1_11
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f109,f106,f111])).

fof(f106,plain,
    ( spl1_10
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | sK0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f109,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_10 ),
    inference(resolution,[],[f107,f42])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | sK0 = k7_relat_1(sK0,X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl1_10
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f84,f45,f106])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | sK0 = k7_relat_1(sK0,X0) )
    | ~ spl1_1 ),
    inference(resolution,[],[f38,f47])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f102,plain,
    ( ~ spl1_8
    | ~ spl1_9
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f93,f80,f99,f95])).

fof(f80,plain,
    ( spl1_6
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f93,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f92,f82])).

fof(f82,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f92,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f30,f82])).

fof(f30,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f91,plain,
    ( spl1_7
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f74,f45,f89])).

fof(f74,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl1_1 ),
    inference(resolution,[],[f37,f47])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f83,plain,
    ( spl1_6
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f78,f55,f50,f45,f80])).

fof(f50,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f55,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f78,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f77,f47])).

fof(f77,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f76,f52])).

fof(f52,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f76,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f36,f57])).

fof(f57,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f73,plain,
    ( spl1_5
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f66,f45,f70])).

fof(f66,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f33,f47])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f65,plain,
    ( spl1_4
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f59,f45,f62])).

fof(f59,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f32,f47])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (18330)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (18329)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (18335)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (18334)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (18339)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (18330)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f48,f53,f58,f65,f73,f83,f91,f102,f108,f114,f148,f231,f237,f278,f291])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    ~spl1_1 | spl1_9 | ~spl1_29),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f290])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    $false | (~spl1_1 | spl1_9 | ~spl1_29)),
% 0.20/0.51    inference(subsumption_resolution,[],[f289,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (~spl1_1 | spl1_9 | ~spl1_29)),
% 0.20/0.51    inference(subsumption_resolution,[],[f285,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f99])).
% 0.20/0.51  % (18333)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl1_9 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (~spl1_1 | ~spl1_29)),
% 0.20/0.51    inference(resolution,[],[f277,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v1_relat_1(sK0) | ~spl1_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl1_1 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))) ) | ~spl1_29),
% 0.20/0.51    inference(avatar_component_clause,[],[f276])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    spl1_29 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_29])])).
% 0.20/0.51  fof(f278,plain,(
% 0.20/0.51    spl1_29 | ~spl1_1 | ~spl1_4 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f166,f70,f62,f45,f276])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl1_4 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl1_5 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) | ~v1_relat_1(X0)) ) | (~spl1_1 | ~spl1_4 | ~spl1_5)),
% 0.20/0.51    inference(forward_demodulation,[],[f165,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(X0))) ) | (~spl1_1 | ~spl1_4)),
% 0.20/0.51    inference(forward_demodulation,[],[f163,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(X0))) ) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f104,f47])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k1_relat_1(k4_relat_1(X1)) = k1_relat_1(k5_relat_1(k4_relat_1(X1),X2)) | ~r1_tarski(k2_relat_1(k4_relat_1(X1)),k1_relat_1(X2))) )),
% 0.20/0.51    inference(resolution,[],[f35,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    ~spl1_1 | spl1_8 | ~spl1_16 | ~spl1_24),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f236])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    $false | (~spl1_1 | spl1_8 | ~spl1_16 | ~spl1_24)),
% 0.20/0.51    inference(subsumption_resolution,[],[f235,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl1_8 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_1 | ~spl1_16 | ~spl1_24)),
% 0.20/0.51    inference(forward_demodulation,[],[f232,f147])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl1_16 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl1_1 | ~spl1_24)),
% 0.20/0.51    inference(resolution,[],[f230,f47])).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0))) ) | ~spl1_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f229])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    spl1_24 <=> ! [X0] : (k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0)) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    spl1_24 | ~spl1_1 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f162,f70,f45,f229])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0)) | ~v1_relat_1(X0)) ) | (~spl1_1 | ~spl1_5)),
% 0.20/0.51    inference(forward_demodulation,[],[f160,f72])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k2_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(X0)) ) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f87,f47])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X2) | k2_relat_1(k5_relat_1(k4_relat_1(X2),X1)) = k9_relat_1(X1,k2_relat_1(k4_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(resolution,[],[f34,f31])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    spl1_16 | ~spl1_7 | ~spl1_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f118,f111,f89,f145])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl1_7 <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl1_11 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl1_7 | ~spl1_11)),
% 0.20/0.51    inference(superposition,[],[f90,f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f111])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl1_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl1_11 | ~spl1_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f109,f106,f111])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl1_10 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_10),
% 0.20/0.51    inference(resolution,[],[f107,f42])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0)) ) | ~spl1_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f106])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl1_10 | ~spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f84,f45,f106])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0)) ) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f38,f47])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~spl1_8 | ~spl1_9 | ~spl1_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f93,f80,f99,f95])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl1_6 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~spl1_6),
% 0.20/0.51    inference(forward_demodulation,[],[f92,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~spl1_6),
% 0.20/0.51    inference(forward_demodulation,[],[f30,f82])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl1_7 | ~spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f74,f45,f89])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f37,f47])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl1_6 | ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f78,f55,f50,f45,f80])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl1_2 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl1_3 <=> v2_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl1_1 | ~spl1_2 | ~spl1_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f77,f47])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f76,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v1_funct_1(sK0) | ~spl1_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.51    inference(resolution,[],[f36,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    v2_funct_1(sK0) | ~spl1_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl1_5 | ~spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f66,f45,f70])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f33,f47])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl1_4 | ~spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f45,f62])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_1),
% 0.20/0.51    inference(resolution,[],[f32,f47])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f55])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    v2_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl1_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f50])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    spl1_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f45])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (18330)------------------------------
% 0.20/0.51  % (18330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18330)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (18330)Memory used [KB]: 6268
% 0.20/0.51  % (18330)Time elapsed: 0.101 s
% 0.20/0.51  % (18330)------------------------------
% 0.20/0.51  % (18330)------------------------------
% 0.20/0.51  % (18352)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (18344)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (18351)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (18342)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (18345)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (18346)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (18336)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (18354)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (18332)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (18325)Success in time 0.161 s
%------------------------------------------------------------------------------
