%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 161 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 461 expanded)
%              Number of equality atoms :   96 ( 176 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f66,f73,f99,f103,f109,f113,f150])).

fof(f150,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f125,f92,f88,f58])).

fof(f58,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_4
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f92,plain,
    ( spl3_5
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f125,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f40,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f113,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f111,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(f111,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(superposition,[],[f108,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f108,plain,
    ( k11_relat_1(sK1,sK0) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_7
  <=> k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f109,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | spl3_6 ),
    inference(avatar_split_clause,[],[f104,f96,f106,f58])).

fof(f96,plain,
    ( spl3_6
  <=> k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f104,plain,
    ( k11_relat_1(sK1,sK0) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_6 ),
    inference(superposition,[],[f98,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f98,plain,
    ( k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k11_relat_1(sK1,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f103,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f90,f30])).

fof(f30,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f99,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f85,f71,f96,f92,f88])).

fof(f71,plain,
    ( spl3_3
  <=> ! [X1,X2] :
        ( k1_funct_1(sK1,X1) = X2
        | ~ r2_hidden(X2,k11_relat_1(sK1,X1))
        | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
        | k1_xboole_0 = k11_relat_1(sK1,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl3_3 ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != X3
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl3_3 ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != X3
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) )
    | ~ spl3_3 ),
    inference(superposition,[],[f51,f75])).

fof(f75,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) = sK2(k11_relat_1(sK1,X2),X3)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) )
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f52])).

% (4211)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f72,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k11_relat_1(sK1,X1))
        | k1_funct_1(sK1,X1) = X2
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f31,f48,f48])).

fof(f31,plain,(
    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f62,f71,f58])).

fof(f62,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(sK1,X1) = X2
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k11_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f60,f28])).

fof(f60,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f64,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f56,f62,f58])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f35,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4202)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (4213)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4205)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (4204)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (4206)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (4220)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (4213)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (4214)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f64,f66,f73,f99,f103,f109,f113,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_4 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f125,f92,f88,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl3_1 <=> v1_relat_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl3_4 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl3_5 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl3_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl3_5),
% 0.21/0.52    inference(superposition,[],[f40,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    $false | spl3_7),
% 0.21/0.52    inference(resolution,[],[f111,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~v1_relat_1(sK1) | spl3_7),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | spl3_7),
% 0.21/0.52    inference(superposition,[],[f108,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f38,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    k11_relat_1(sK1,sK0) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl3_7 <=> k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_7 | spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f104,f96,f106,f58])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl3_6 <=> k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k11_relat_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    k11_relat_1(sK1,sK0) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl3_6),
% 0.21/0.53    inference(superposition,[],[f98,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k11_relat_1(sK1,sK0) | spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    $false | spl3_4),
% 0.21/0.53    inference(resolution,[],[f90,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f88])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~spl3_4 | spl3_5 | ~spl3_6 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f85,f71,f96,f92,f88])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl3_3 <=> ! [X1,X2] : (k1_funct_1(sK1,X1) = X2 | ~r2_hidden(X2,k11_relat_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl3_3),
% 0.21/0.53    inference(superposition,[],[f49,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (k11_relat_1(sK1,X0) = k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k11_relat_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl3_3),
% 0.21/0.53    inference(equality_resolution,[],[f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != X3 | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) | ~r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl3_3),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != X3 | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3) | ~r2_hidden(X2,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)) ) | ~spl3_3),
% 0.21/0.53    inference(superposition,[],[f51,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k1_funct_1(sK1,X2) = sK2(k11_relat_1(sK1,X2),X3) | ~r2_hidden(X2,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X2) | k11_relat_1(sK1,X2) = k2_enumset1(X3,X3,X3,X3)) ) | ~spl3_3),
% 0.21/0.53    inference(resolution,[],[f72,f52])).
% 0.21/0.53  % (4211)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f48])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k11_relat_1(sK1,X1)) | k1_funct_1(sK1,X1) = X2 | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f71])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f48])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f48,f48])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ~spl3_1 | spl3_3 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f68,f62,f71,f58])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl3_2 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k1_funct_1(sK1,X1) = X2 | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X2,k11_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f63,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    $false | spl3_1),
% 0.21/0.53    inference(resolution,[],[f60,f28])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ~spl3_1 | spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f62,f58])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f35,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    v1_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = X2 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4213)------------------------------
% 0.21/0.53  % (4213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4213)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4213)Memory used [KB]: 6268
% 0.21/0.53  % (4213)Time elapsed: 0.100 s
% 0.21/0.53  % (4213)------------------------------
% 0.21/0.53  % (4213)------------------------------
% 0.21/0.53  % (4223)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (4200)Success in time 0.164 s
%------------------------------------------------------------------------------
