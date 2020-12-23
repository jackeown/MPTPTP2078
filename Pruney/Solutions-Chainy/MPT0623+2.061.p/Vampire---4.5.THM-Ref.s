%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 132 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  277 ( 548 expanded)
%              Number of equality atoms :  119 ( 249 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f157,f169])).

fof(f169,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f167,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f167,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f166,f36])).

fof(f36,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f166,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f163,f115])).

fof(f115,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK3(X0) ) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK3(X0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f38,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f163,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f83,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f83,plain,(
    ~ r1_tarski(k2_relat_1(sK3(sK1)),sK0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f81,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK3(X0)),sK0)
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0)) ) ),
    inference(superposition,[],[f34,f46])).

fof(f34,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f157,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f139,f64])).

fof(f64,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | spl7_2 ),
    inference(resolution,[],[f114,f103])).

fof(f103,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl7_2 ),
    inference(resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f99,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f97,f78])).

fof(f78,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(X0),sK0)
        | k1_xboole_0 = sK1 )
    | spl7_2 ),
    inference(superposition,[],[f96,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

% (27296)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (27293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (27307)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (27307)Refutation not found, incomplete strategy% (27307)------------------------------
% (27307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27307)Termination reason: Refutation not found, incomplete strategy

% (27307)Memory used [KB]: 10618
% (27307)Time elapsed: 0.083 s
% (27307)------------------------------
% (27307)------------------------------
% (27292)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f96,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f95,f78])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f93,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | ~ v1_funct_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    ! [X4] :
      ( r2_hidden(sK4(k1_xboole_0,X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f111,f35])).

fof(f35,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f111,plain,(
    ! [X4] :
      ( k1_relat_1(k1_xboole_0) = X4
      | r2_hidden(sK4(k1_xboole_0,X4),X4) ) ),
    inference(resolution,[],[f51,f84])).

fof(f84,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f48,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f68,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f33,f66,f63])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (27287)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (27287)Refutation not found, incomplete strategy% (27287)------------------------------
% 0.22/0.48  % (27287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27289)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (27287)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27287)Memory used [KB]: 6140
% 0.22/0.49  % (27287)Time elapsed: 0.056 s
% 0.22/0.49  % (27287)------------------------------
% 0.22/0.49  % (27287)------------------------------
% 0.22/0.50  % (27289)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f68,f157,f169])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~spl7_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    $false | ~spl7_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f167,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,sK0) | ~spl7_2),
% 0.22/0.50    inference(forward_demodulation,[],[f166,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | ~spl7_2),
% 0.22/0.50    inference(forward_demodulation,[],[f163,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    k1_xboole_0 = sK3(k1_xboole_0)),
% 0.22/0.50    inference(equality_resolution,[],[f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK3(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK3(X0) | ~v1_relat_1(sK3(X0))) )),
% 0.22/0.50    inference(superposition,[],[f38,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK3(k1_xboole_0)),sK0) | ~spl7_2),
% 0.22/0.50    inference(backward_demodulation,[],[f83,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK3(sK1)),sK0)),
% 0.22/0.50    inference(equality_resolution,[],[f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK3(X0)),sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f81,f44])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK3(X0)),sK0) | ~v1_relat_1(sK3(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f80,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK3(X0)),sK0) | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0))) )),
% 0.22/0.50    inference(superposition,[],[f34,f46])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl7_1 | spl7_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    $false | (spl7_1 | spl7_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f139,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl7_1 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | spl7_2),
% 0.22/0.50    inference(resolution,[],[f114,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl7_2),
% 0.22/0.50    inference(resolution,[],[f99,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) ) | spl7_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f97,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1) ) | spl7_2),
% 0.22/0.50    inference(superposition,[],[f96,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.22/0.50  % (27296)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (27293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (27307)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (27307)Refutation not found, incomplete strategy% (27307)------------------------------
% 0.22/0.51  % (27307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27307)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27307)Memory used [KB]: 10618
% 0.22/0.51  % (27307)Time elapsed: 0.083 s
% 0.22/0.51  % (27307)------------------------------
% 0.22/0.51  % (27307)------------------------------
% 0.22/0.51  % (27292)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) ) | spl7_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f95,f78])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) | k1_xboole_0 = sK1) )),
% 0.22/0.51    inference(equality_resolution,[],[f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X2,X3] : (sK1 != X2 | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | k1_xboole_0 = X2) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f93,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X2,X3] : (sK1 != X2 | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X2,X3] : (sK1 != X2 | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | ~v1_funct_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.22/0.51    inference(superposition,[],[f34,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X4] : (r2_hidden(sK4(k1_xboole_0,X4),X4) | k1_xboole_0 = X4) )),
% 0.22/0.51    inference(forward_demodulation,[],[f111,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X4] : (k1_relat_1(k1_xboole_0) = X4 | r2_hidden(sK4(k1_xboole_0,X4),X4)) )),
% 0.22/0.51    inference(resolution,[],[f51,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(superposition,[],[f48,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.51    inference(rectify,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~spl7_1 | spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f66,f63])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27289)------------------------------
% 0.22/0.51  % (27289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27289)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27289)Memory used [KB]: 10618
% 0.22/0.51  % (27289)Time elapsed: 0.076 s
% 0.22/0.51  % (27289)------------------------------
% 0.22/0.51  % (27289)------------------------------
% 0.22/0.51  % (27286)Success in time 0.152 s
%------------------------------------------------------------------------------
