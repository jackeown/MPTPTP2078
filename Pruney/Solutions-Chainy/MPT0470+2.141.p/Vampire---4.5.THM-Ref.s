%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 124 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 352 expanded)
%              Number of equality atoms :   67 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f76,f96,f110,f131,f159])).

fof(f159,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f157,f129,f56,f49])).

fof(f49,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f56,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f129,plain,
    ( spl1_12
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f157,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(resolution,[],[f151,f57])).

fof(f57,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl1_12 ),
    inference(resolution,[],[f130,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( ~ spl1_7
    | ~ spl1_4
    | spl1_12
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f127,f68,f64,f129,f60,f74])).

fof(f74,plain,
    ( spl1_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f60,plain,
    ( spl1_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f64,plain,
    ( spl1_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f68,plain,
    ( spl1_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f125,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl1_6 ),
    inference(superposition,[],[f87,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f85,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

% (24339)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f85,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_xboole_0(k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f42,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | v1_xboole_0(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f110,plain,
    ( spl1_2
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f104,f94,f56,f52])).

fof(f52,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f94,plain,
    ( spl1_8
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f104,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(resolution,[],[f98,f57])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl1_8 ),
    inference(resolution,[],[f95,f35])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( ~ spl1_7
    | ~ spl1_4
    | spl1_8
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f90,f68,f64,f94,f60,f74])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f88,f69])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl1_5 ),
    inference(superposition,[],[f86,f65])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X1,X0) ) ),
    inference(resolution,[],[f83,f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_xboole_0(k2_relat_1(X1))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f42,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_relat_1(X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | v1_xboole_0(k5_relat_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f40,f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f76,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f72,f74])).

fof(f72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f41,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f66,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f54,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f31,f52,f49])).

fof(f31,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (24348)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (24337)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (24337)Refutation not found, incomplete strategy% (24337)------------------------------
% 0.22/0.48  % (24337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24337)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (24337)Memory used [KB]: 10490
% 0.22/0.48  % (24337)Time elapsed: 0.067 s
% 0.22/0.48  % (24337)------------------------------
% 0.22/0.48  % (24337)------------------------------
% 0.22/0.49  % (24352)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (24338)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (24341)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (24350)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (24342)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (24340)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (24342)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f76,f96,f110,f131,f159])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl1_1 | ~spl1_3 | ~spl1_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f157,f129,f56,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl1_3 <=> v1_relat_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl1_12 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_3 | ~spl1_12)),
% 0.22/0.50    inference(resolution,[],[f151,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_relat_1(sK0) | ~spl1_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl1_12),
% 0.22/0.50    inference(resolution,[],[f130,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | ~spl1_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f129])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~spl1_7 | ~spl1_4 | spl1_12 | ~spl1_5 | ~spl1_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f127,f68,f64,f129,f60,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl1_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl1_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl1_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl1_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f125,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f64])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.22/0.50    inference(superposition,[],[f87,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f85,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  % (24339)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X0,X1)) | ~v1_xboole_0(k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(global_subsumption,[],[f42,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(k5_relat_1(X0,X1)) | v1_xboole_0(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(superposition,[],[f39,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl1_2 | ~spl1_3 | ~spl1_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f104,f94,f56,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl1_8 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_3 | ~spl1_8)),
% 0.22/0.50    inference(resolution,[],[f98,f57])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl1_8),
% 0.22/0.50    inference(resolution,[],[f95,f35])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ~spl1_7 | ~spl1_4 | spl1_8 | ~spl1_5 | ~spl1_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f68,f64,f94,f60,f74])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | (~spl1_5 | ~spl1_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f88,f69])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl1_5),
% 0.22/0.50    inference(superposition,[],[f86,f65])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(k2_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f83,f36])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(k5_relat_1(X0,X1)) | ~v1_xboole_0(k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(global_subsumption,[],[f42,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(k2_relat_1(X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | v1_xboole_0(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(superposition,[],[f40,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl1_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f72,f74])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(superposition,[],[f41,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl1_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f68])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl1_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f64])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl1_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f60])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f56])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~spl1_1 | ~spl1_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f52,f49])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24342)------------------------------
% 0.22/0.50  % (24342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24342)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24342)Memory used [KB]: 10618
% 0.22/0.50  % (24342)Time elapsed: 0.037 s
% 0.22/0.50  % (24342)------------------------------
% 0.22/0.50  % (24342)------------------------------
% 0.22/0.50  % (24332)Success in time 0.14 s
%------------------------------------------------------------------------------
