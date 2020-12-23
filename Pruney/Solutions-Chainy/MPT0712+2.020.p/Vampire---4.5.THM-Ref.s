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
% DateTime   : Thu Dec  3 12:54:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 156 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  218 ( 369 expanded)
%              Number of equality atoms :   54 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f85,f90,f166,f192])).

fof(f192,plain,
    ( ~ spl2_1
    | spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl2_1
    | spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f190,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ spl2_1
    | spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f84,f189])).

fof(f189,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f188,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_6
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f188,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f77,f165])).

fof(f165,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl2_7
  <=> k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f77,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_5
  <=> r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f166,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f129,f82,f55,f50,f163])).

fof(f55,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f129,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_5 ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_5 ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_5 ),
    inference(superposition,[],[f84,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))
        | k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))
        | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) )
    | ~ spl2_1 ),
    inference(factoring,[],[f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

% (21462)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f33,f52])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))
        | k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f100,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) = k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f91,f52])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) = k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f40,f42,f42])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f90,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f65,f60,f87])).

fof(f60,plain,
    ( spl2_3
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f65,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f32,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f85,plain,
    ( ~ spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f79,f50,f82])).

fof(f79,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f44,f77])).

fof(f44,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f27,f43,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f63,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21470)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % (21478)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.46  % (21470)Refutation not found, incomplete strategy% (21470)------------------------------
% 0.21/0.46  % (21470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (21470)Memory used [KB]: 10618
% 0.21/0.46  % (21470)Time elapsed: 0.057 s
% 0.21/0.46  % (21470)------------------------------
% 0.21/0.46  % (21470)------------------------------
% 0.21/0.52  % (21478)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f53,f58,f63,f85,f90,f166,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~spl2_1 | spl2_5 | ~spl2_6 | ~spl2_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    $false | (~spl2_1 | spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f190,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | (~spl2_1 | spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.21/0.52    inference(backward_demodulation,[],[f84,f189])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    k1_xboole_0 = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_6 | ~spl2_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f188,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl2_6 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_7)),
% 0.21/0.52    inference(superposition,[],[f77,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl2_7 <=> k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f52,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl2_5 <=> r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl2_7 | ~spl2_1 | ~spl2_2 | spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f82,f55,f50,f163])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_2 | spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_2 | spl2_5)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_2 | spl2_5)),
% 0.21/0.52    inference(superposition,[],[f84,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) | k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1))) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.52    inference(resolution,[],[f101,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) ) | ~spl2_1),
% 0.21/0.52    inference(factoring,[],[f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))) ) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f80,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f41,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.53  % (21462)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f20])).
% 1.31/0.53  fof(f20,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f6])).
% 1.31/0.53  fof(f6,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.31/0.53  fof(f80,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl2_1),
% 1.31/0.53    inference(resolution,[],[f33,f52])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.31/0.53  fof(f101,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) | k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2)),
% 1.31/0.53    inference(resolution,[],[f100,f92])).
% 1.31/0.53  fof(f92,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) = k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0))) ) | (~spl2_1 | ~spl2_2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f91,f52])).
% 1.31/0.53  fof(f91,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) = k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) | ~v1_relat_1(sK1)) ) | ~spl2_2),
% 1.31/0.53    inference(resolution,[],[f45,f57])).
% 1.31/0.53  fof(f57,plain,(
% 1.31/0.53    v1_funct_1(sK1) | ~spl2_2),
% 1.31/0.53    inference(avatar_component_clause,[],[f55])).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f40,f42,f42])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f19])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.31/0.53    inference(flattening,[],[f18])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.31/0.53    inference(ennf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 1.31/0.53  fof(f90,plain,(
% 1.31/0.53    spl2_6 | ~spl2_3),
% 1.31/0.53    inference(avatar_split_clause,[],[f65,f60,f87])).
% 1.31/0.53  fof(f60,plain,(
% 1.31/0.53    spl2_3 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.31/0.53  fof(f65,plain,(
% 1.31/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_3),
% 1.31/0.53    inference(superposition,[],[f32,f62])).
% 1.31/0.53  fof(f62,plain,(
% 1.31/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl2_3),
% 1.31/0.53    inference(avatar_component_clause,[],[f60])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.31/0.53  fof(f85,plain,(
% 1.31/0.53    ~spl2_5 | ~spl2_1),
% 1.31/0.53    inference(avatar_split_clause,[],[f79,f50,f82])).
% 1.31/0.53  fof(f79,plain,(
% 1.31/0.53    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | ~spl2_1),
% 1.31/0.53    inference(backward_demodulation,[],[f44,f77])).
% 1.31/0.53  fof(f44,plain,(
% 1.31/0.53    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.31/0.53    inference(definition_unfolding,[],[f27,f43,f43])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.31/0.53    inference(definition_unfolding,[],[f30,f42])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.31/0.53    inference(cnf_transformation,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.31/0.53    inference(flattening,[],[f14])).
% 1.31/0.53  fof(f14,plain,(
% 1.31/0.53    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,negated_conjecture,(
% 1.31/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.31/0.53    inference(negated_conjecture,[],[f12])).
% 1.31/0.53  fof(f12,conjecture,(
% 1.31/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 1.31/0.53  fof(f63,plain,(
% 1.31/0.53    spl2_3),
% 1.31/0.53    inference(avatar_split_clause,[],[f28,f60])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.31/0.53    inference(cnf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.31/0.53  fof(f58,plain,(
% 1.31/0.53    spl2_2),
% 1.31/0.53    inference(avatar_split_clause,[],[f26,f55])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    v1_funct_1(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f22])).
% 1.31/0.53  fof(f53,plain,(
% 1.31/0.53    spl2_1),
% 1.31/0.53    inference(avatar_split_clause,[],[f25,f50])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    v1_relat_1(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f22])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (21478)------------------------------
% 1.31/0.53  % (21478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (21478)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (21478)Memory used [KB]: 10874
% 1.31/0.53  % (21478)Time elapsed: 0.123 s
% 1.31/0.53  % (21478)------------------------------
% 1.31/0.53  % (21478)------------------------------
% 1.31/0.53  % (21457)Success in time 0.172 s
%------------------------------------------------------------------------------
