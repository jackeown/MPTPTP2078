%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:44 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 252 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 ( 558 expanded)
%              Number of equality atoms :   87 ( 218 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f141,f149,f158,f326,f337,f340,f493,f500])).

fof(f500,plain,
    ( ~ spl3_13
    | ~ spl3_7
    | spl3_19 ),
    inference(avatar_split_clause,[],[f498,f490,f135,f334])).

fof(f334,plain,
    ( spl3_13
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f135,plain,
    ( spl3_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f490,plain,
    ( spl3_19
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f498,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl3_19 ),
    inference(resolution,[],[f492,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f492,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f490])).

fof(f493,plain,
    ( ~ spl3_19
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f488,f156,f90,f490])).

fof(f90,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f156,plain,
    ( spl3_9
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f488,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f487,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f49,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f487,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f484,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f484,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_9 ),
    inference(superposition,[],[f80,f479])).

fof(f479,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_9 ),
    inference(resolution,[],[f293,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f293,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X2,k1_xboole_0)) )
    | ~ spl3_9 ),
    inference(resolution,[],[f288,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f288,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f262,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f262,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X5)
      | X4 = X5
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

% (3236)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f99,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(X2,X1),X2)
      | ~ r1_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f61,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (3230)Refutation not found, incomplete strategy% (3230)------------------------------
% (3230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3230)Termination reason: Refutation not found, incomplete strategy

% (3230)Memory used [KB]: 1663
% (3230)Time elapsed: 0.142 s
% (3230)------------------------------
% (3230)------------------------------
fof(f80,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f51,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f340,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f336,f44])).

fof(f336,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f334])).

fof(f337,plain,
    ( ~ spl3_7
    | ~ spl3_13
    | spl3_10 ),
    inference(avatar_split_clause,[],[f331,f317,f334,f135])).

fof(f317,plain,
    ( spl3_10
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f331,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl3_10 ),
    inference(resolution,[],[f319,f58])).

fof(f319,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f317])).

fof(f326,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f325,f139,f86,f317])).

fof(f86,plain,
    ( spl3_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f139,plain,
    ( spl3_8
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f325,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f324,f79])).

fof(f324,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f313,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f313,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f80,f306])).

fof(f306,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_8 ),
    inference(resolution,[],[f292,f44])).

fof(f292,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f288,f140])).

fof(f140,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f158,plain,
    ( ~ spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f154,f156,f135])).

fof(f154,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f53,f48])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f149,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f146,f46])).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_7 ),
    inference(resolution,[],[f137,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f137,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f141,plain,
    ( ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

% (3227)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f133,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f52,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f93,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f90,f86])).

fof(f45,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (3225)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (3221)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (3217)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (3233)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (3219)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.21/0.52  % (3214)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.52  % (3220)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.53  % (3209)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (3211)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.53  % (3229)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.21/0.53  % (3232)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.53  % (3211)Refutation not found, incomplete strategy% (3211)------------------------------
% 1.21/0.53  % (3211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (3211)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (3211)Memory used [KB]: 10618
% 1.21/0.53  % (3211)Time elapsed: 0.125 s
% 1.21/0.53  % (3211)------------------------------
% 1.21/0.53  % (3211)------------------------------
% 1.21/0.53  % (3230)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.21/0.53  % (3210)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.53  % (3213)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.53  % (3231)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.53  % (3216)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.53  % (3222)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.54  % (3215)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.54  % (3212)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.54  % (3223)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.54  % (3224)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.54  % (3221)Refutation found. Thanks to Tanya!
% 1.21/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % (3234)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.55  % (3218)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.55  % (3226)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.55  % (3238)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (3235)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.55  % (3229)Refutation not found, incomplete strategy% (3229)------------------------------
% 1.44/0.55  % (3229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (3231)Refutation not found, incomplete strategy% (3231)------------------------------
% 1.44/0.55  % (3231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (3231)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (3231)Memory used [KB]: 10618
% 1.44/0.55  % (3231)Time elapsed: 0.107 s
% 1.44/0.55  % (3231)------------------------------
% 1.44/0.55  % (3231)------------------------------
% 1.44/0.55  % (3237)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.55  % (3229)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (3229)Memory used [KB]: 10746
% 1.44/0.55  % (3229)Time elapsed: 0.149 s
% 1.44/0.55  % (3229)------------------------------
% 1.44/0.55  % (3229)------------------------------
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f501,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f93,f141,f149,f158,f326,f337,f340,f493,f500])).
% 1.44/0.55  fof(f500,plain,(
% 1.44/0.55    ~spl3_13 | ~spl3_7 | spl3_19),
% 1.44/0.55    inference(avatar_split_clause,[],[f498,f490,f135,f334])).
% 1.44/0.55  fof(f334,plain,(
% 1.44/0.55    spl3_13 <=> v1_relat_1(sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.44/0.55  fof(f135,plain,(
% 1.44/0.55    spl3_7 <=> v1_relat_1(k1_xboole_0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.44/0.55  fof(f490,plain,(
% 1.44/0.55    spl3_19 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.44/0.55  fof(f498,plain,(
% 1.44/0.55    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl3_19),
% 1.44/0.55    inference(resolution,[],[f492,f58])).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f28])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.44/0.55    inference(flattening,[],[f27])).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f15])).
% 1.44/0.55  fof(f15,axiom,(
% 1.44/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.44/0.55  fof(f492,plain,(
% 1.44/0.55    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl3_19),
% 1.44/0.55    inference(avatar_component_clause,[],[f490])).
% 1.44/0.55  fof(f493,plain,(
% 1.44/0.55    ~spl3_19 | spl3_2 | ~spl3_9),
% 1.44/0.55    inference(avatar_split_clause,[],[f488,f156,f90,f490])).
% 1.44/0.55  fof(f90,plain,(
% 1.44/0.55    spl3_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.55  fof(f156,plain,(
% 1.44/0.55    spl3_9 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.44/0.55  fof(f488,plain,(
% 1.44/0.55    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_9),
% 1.44/0.55    inference(forward_demodulation,[],[f487,f79])).
% 1.44/0.55  fof(f79,plain,(
% 1.44/0.55    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f49,f78])).
% 1.44/0.55  fof(f78,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f56,f77])).
% 1.44/0.55  fof(f77,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f57,f76])).
% 1.44/0.55  fof(f76,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f68,f75])).
% 1.44/0.55  fof(f75,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f69,f74])).
% 1.44/0.55  fof(f74,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f70,f73])).
% 1.44/0.55  fof(f73,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f71,f72])).
% 1.44/0.55  fof(f72,plain,(
% 1.44/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f11])).
% 1.44/0.55  fof(f11,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.44/0.55  fof(f71,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f10])).
% 1.44/0.55  fof(f10,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.44/0.55  fof(f70,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.44/0.55  fof(f69,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.55  fof(f68,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.55  fof(f57,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,axiom,(
% 1.44/0.55    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.44/0.55  fof(f487,plain,(
% 1.44/0.55    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_9),
% 1.44/0.55    inference(forward_demodulation,[],[f484,f83])).
% 1.44/0.55  fof(f83,plain,(
% 1.44/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f67])).
% 1.44/0.55  fof(f67,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f43])).
% 1.44/0.55  fof(f43,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.44/0.55    inference(flattening,[],[f42])).
% 1.44/0.55  fof(f42,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.44/0.55    inference(nnf_transformation,[],[f12])).
% 1.44/0.55  fof(f12,axiom,(
% 1.44/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.44/0.55  fof(f484,plain,(
% 1.44/0.55    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_9),
% 1.44/0.55    inference(superposition,[],[f80,f479])).
% 1.44/0.55  fof(f479,plain,(
% 1.44/0.55    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_9),
% 1.44/0.55    inference(resolution,[],[f293,f44])).
% 1.44/0.55  fof(f44,plain,(
% 1.44/0.55    v1_relat_1(sK0)),
% 1.44/0.55    inference(cnf_transformation,[],[f31])).
% 1.44/0.55  fof(f31,plain,(
% 1.44/0.55    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f21])).
% 1.44/0.55  fof(f21,negated_conjecture,(
% 1.44/0.55    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.44/0.55    inference(negated_conjecture,[],[f20])).
% 1.44/0.55  fof(f20,conjecture,(
% 1.44/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.44/0.55  fof(f293,plain,(
% 1.44/0.55    ( ! [X2] : (~v1_relat_1(X2) | k1_xboole_0 = k2_relat_1(k5_relat_1(X2,k1_xboole_0))) ) | ~spl3_9),
% 1.44/0.55    inference(resolution,[],[f288,f157])).
% 1.44/0.55  fof(f157,plain,(
% 1.44/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_9),
% 1.44/0.55    inference(avatar_component_clause,[],[f156])).
% 1.44/0.55  fof(f288,plain,(
% 1.44/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.44/0.55    inference(resolution,[],[f262,f46])).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    v1_xboole_0(k1_xboole_0)),
% 1.44/0.55    inference(cnf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    v1_xboole_0(k1_xboole_0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.44/0.55  fof(f262,plain,(
% 1.44/0.55    ( ! [X4,X5] : (~v1_xboole_0(X5) | X4 = X5 | ~r1_tarski(X4,X5)) )),
% 1.44/0.55    inference(resolution,[],[f99,f54])).
% 1.44/0.55  fof(f54,plain,(
% 1.44/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  % (3236)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.55    inference(rectify,[],[f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.55    inference(nnf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.55  fof(f99,plain,(
% 1.44/0.55    ( ! [X2,X1] : (r2_hidden(sK2(X2,X1),X2) | ~r1_tarski(X1,X2) | X1 = X2) )),
% 1.44/0.55    inference(resolution,[],[f61,f63])).
% 1.44/0.55  fof(f63,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f41])).
% 1.44/0.55  fof(f41,plain,(
% 1.44/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 1.44/0.55  fof(f40,plain,(
% 1.44/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f39,plain,(
% 1.44/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.55    inference(rectify,[],[f38])).
% 1.44/0.55  fof(f38,plain,(
% 1.44/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.55    inference(nnf_transformation,[],[f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.44/0.55  fof(f61,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f37])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.55    inference(flattening,[],[f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.55    inference(nnf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.55  % (3230)Refutation not found, incomplete strategy% (3230)------------------------------
% 1.44/0.55  % (3230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (3230)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (3230)Memory used [KB]: 1663
% 1.44/0.55  % (3230)Time elapsed: 0.142 s
% 1.44/0.55  % (3230)------------------------------
% 1.44/0.55  % (3230)------------------------------
% 1.44/0.55  fof(f80,plain,(
% 1.44/0.55    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f51,f78])).
% 1.44/0.55  fof(f51,plain,(
% 1.44/0.55    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f16])).
% 1.44/0.55  fof(f16,axiom,(
% 1.44/0.55    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.44/0.55  fof(f340,plain,(
% 1.44/0.55    spl3_13),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f338])).
% 1.44/0.55  fof(f338,plain,(
% 1.44/0.55    $false | spl3_13),
% 1.44/0.55    inference(resolution,[],[f336,f44])).
% 1.44/0.55  fof(f336,plain,(
% 1.44/0.55    ~v1_relat_1(sK0) | spl3_13),
% 1.44/0.55    inference(avatar_component_clause,[],[f334])).
% 1.44/0.55  fof(f337,plain,(
% 1.44/0.55    ~spl3_7 | ~spl3_13 | spl3_10),
% 1.44/0.55    inference(avatar_split_clause,[],[f331,f317,f334,f135])).
% 1.44/0.55  fof(f317,plain,(
% 1.44/0.55    spl3_10 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.44/0.55  fof(f331,plain,(
% 1.44/0.55    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl3_10),
% 1.44/0.55    inference(resolution,[],[f319,f58])).
% 1.44/0.55  fof(f319,plain,(
% 1.44/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl3_10),
% 1.44/0.55    inference(avatar_component_clause,[],[f317])).
% 1.44/0.55  fof(f326,plain,(
% 1.44/0.55    ~spl3_10 | spl3_1 | ~spl3_8),
% 1.44/0.55    inference(avatar_split_clause,[],[f325,f139,f86,f317])).
% 1.44/0.55  fof(f86,plain,(
% 1.44/0.55    spl3_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.55  fof(f139,plain,(
% 1.44/0.55    spl3_8 <=> ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.44/0.55  fof(f325,plain,(
% 1.44/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_8),
% 1.44/0.55    inference(forward_demodulation,[],[f324,f79])).
% 1.44/0.55  fof(f324,plain,(
% 1.44/0.55    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_8),
% 1.44/0.55    inference(forward_demodulation,[],[f313,f84])).
% 1.44/0.55  fof(f84,plain,(
% 1.44/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.44/0.55    inference(equality_resolution,[],[f66])).
% 1.44/0.55  fof(f66,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f43])).
% 1.44/0.55  fof(f313,plain,(
% 1.44/0.55    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_8),
% 1.44/0.55    inference(superposition,[],[f80,f306])).
% 1.44/0.55  fof(f306,plain,(
% 1.44/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_8),
% 1.44/0.55    inference(resolution,[],[f292,f44])).
% 1.44/0.55  fof(f292,plain,(
% 1.44/0.55    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1))) ) | ~spl3_8),
% 1.44/0.55    inference(resolution,[],[f288,f140])).
% 1.44/0.55  fof(f140,plain,(
% 1.44/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_8),
% 1.44/0.55    inference(avatar_component_clause,[],[f139])).
% 1.44/0.55  fof(f158,plain,(
% 1.44/0.55    ~spl3_7 | spl3_9),
% 1.44/0.55    inference(avatar_split_clause,[],[f154,f156,f135])).
% 1.44/0.55  fof(f154,plain,(
% 1.44/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.44/0.55    inference(superposition,[],[f53,f48])).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.44/0.55    inference(cnf_transformation,[],[f19])).
% 1.44/0.55  fof(f19,axiom,(
% 1.44/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.44/0.55  fof(f53,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f26])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,axiom,(
% 1.44/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.44/0.55  fof(f149,plain,(
% 1.44/0.55    spl3_7),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f147])).
% 1.44/0.55  fof(f147,plain,(
% 1.44/0.55    $false | spl3_7),
% 1.44/0.55    inference(resolution,[],[f146,f46])).
% 1.44/0.55  fof(f146,plain,(
% 1.44/0.55    ~v1_xboole_0(k1_xboole_0) | spl3_7),
% 1.44/0.55    inference(resolution,[],[f137,f50])).
% 1.44/0.55  fof(f50,plain,(
% 1.44/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f23])).
% 1.44/0.55  fof(f23,plain,(
% 1.44/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f14])).
% 1.44/0.55  fof(f14,axiom,(
% 1.44/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.44/0.55  fof(f137,plain,(
% 1.44/0.55    ~v1_relat_1(k1_xboole_0) | spl3_7),
% 1.44/0.55    inference(avatar_component_clause,[],[f135])).
% 1.44/0.55  fof(f141,plain,(
% 1.44/0.55    ~spl3_7 | spl3_8),
% 1.44/0.55    inference(avatar_split_clause,[],[f133,f139,f135])).
% 1.44/0.56  % (3227)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.56  fof(f133,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.44/0.56    inference(superposition,[],[f52,f47])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,axiom,(
% 1.44/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.44/0.56  fof(f93,plain,(
% 1.44/0.56    ~spl3_1 | ~spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f45,f90,f86])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f31])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (3221)------------------------------
% 1.44/0.56  % (3221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (3221)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (3221)Memory used [KB]: 6396
% 1.44/0.56  % (3221)Time elapsed: 0.143 s
% 1.44/0.56  % (3221)------------------------------
% 1.44/0.56  % (3221)------------------------------
% 1.44/0.56  % (3208)Success in time 0.196 s
%------------------------------------------------------------------------------
