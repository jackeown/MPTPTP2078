%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 140 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  298 ( 400 expanded)
%              Number of equality atoms :   79 ( 112 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f104,f113,f118,f122,f130,f172])).

fof(f172,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f168,f116,f66,f59])).

fof(f59,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( spl4_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f168,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f157,f67])).

fof(f67,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f117,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f130,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f126,f102,f66,f62])).

fof(f62,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f126,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f123,f67])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl4_8 ),
    inference(resolution,[],[f103,f42])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f122,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_9 ),
    inference(resolution,[],[f112,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f51,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f112,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_9
  <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f118,plain,
    ( ~ spl4_7
    | ~ spl4_4
    | spl4_10
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f114,f78,f74,f116,f70,f98])).

fof(f98,plain,
    ( spl4_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f70,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( spl4_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f106,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f93,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_xboole_0(k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f52,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | v1_xboole_0(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f113,plain,
    ( spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f109,f98,f111])).

fof(f109,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl4_7 ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f104,plain,
    ( ~ spl4_7
    | ~ spl4_4
    | spl4_8
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f96,f78,f74,f102,f70,f98])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f94,f79])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl4_5 ),
    inference(superposition,[],[f92,f75])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X1,X0) ) ),
    inference(resolution,[],[f89,f45])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_xboole_0(k2_relat_1(X1))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f52,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_relat_1(X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | v1_xboole_0(k5_relat_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f80,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f76,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f68,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f64,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f38,f62,f59])).

fof(f38,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (6477)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (6474)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (6476)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (6475)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (6482)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (6485)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (6484)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (6483)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (6475)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f104,f113,f118,f122,f130,f172])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl4_1 | ~spl4_3 | ~spl4_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f168,f116,f66,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl4_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl4_3 <=> v1_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl4_10 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl4_3 | ~spl4_10)),
% 0.22/0.53    inference(resolution,[],[f157,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    v1_relat_1(sK0) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f66])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl4_10),
% 0.22/0.53    inference(resolution,[],[f117,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | ~spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    spl4_2 | ~spl4_3 | ~spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f126,f102,f66,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    spl4_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl4_8 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl4_3 | ~spl4_8)),
% 0.22/0.53    inference(resolution,[],[f123,f67])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl4_8),
% 0.22/0.53    inference(resolution,[],[f103,f42])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f102])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ~spl4_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    $false | ~spl4_9),
% 0.22/0.53    inference(resolution,[],[f112,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f51,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl4_9 <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~spl4_7 | ~spl4_4 | spl4_10 | ~spl4_5 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f114,f78,f74,f116,f70,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl4_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl4_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl4_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | (~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(forward_demodulation,[],[f106,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl4_6),
% 0.22/0.53    inference(superposition,[],[f93,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f91,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X0,X1)) | ~v1_xboole_0(k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(global_subsumption,[],[f52,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(k5_relat_1(X0,X1)) | v1_xboole_0(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(superposition,[],[f46,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl4_9 | spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f109,f98,f111])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl4_7),
% 0.22/0.53    inference(resolution,[],[f99,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f33,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(rectify,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~v1_relat_1(k1_xboole_0) | spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f98])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ~spl4_7 | ~spl4_4 | spl4_8 | ~spl4_5 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f96,f78,f74,f102,f70,f98])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | (~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(forward_demodulation,[],[f94,f79])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl4_5),
% 0.22/0.53    inference(superposition,[],[f92,f75])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X1,X0)) )),
% 0.22/0.53    inference(resolution,[],[f89,f45])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X0,X1)) | ~v1_xboole_0(k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(global_subsumption,[],[f52,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_relat_1(X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | v1_xboole_0(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(superposition,[],[f47,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f78])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f74])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f70])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f66])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f62,f59])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (6475)------------------------------
% 0.22/0.53  % (6475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6475)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (6475)Memory used [KB]: 10746
% 0.22/0.53  % (6475)Time elapsed: 0.076 s
% 0.22/0.53  % (6475)------------------------------
% 0.22/0.53  % (6475)------------------------------
% 0.22/0.53  % (6468)Success in time 0.167 s
%------------------------------------------------------------------------------
