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
% DateTime   : Thu Dec  3 12:53:42 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 133 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 415 expanded)
%              Number of equality atoms :   49 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f58,f86,f102])).

fof(f102,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f98,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_2 ),
    inference(superposition,[],[f48,f92])).

fof(f92,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f89,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f88,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f88,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f33,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f48,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f46])).

% (12333)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f86,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f84,f25])).

fof(f84,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f81,f55])).

fof(f55,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f81,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f80,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0))
    | spl3_1 ),
    inference(resolution,[],[f75,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k2_relat_1(sK1),X0),k1_enumset1(sK0,sK0,sK0))
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | spl3_1 ),
    inference(resolution,[],[f73,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k1_enumset1(sK0,sK0,sK0)) )
    | spl3_1 ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,
    ( r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_relat_1(sK1))
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_relat_1(sK1))
    | spl3_1 ),
    inference(superposition,[],[f37,f67])).

fof(f67,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_relat_1(sK1))
    | spl3_1 ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f60,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | k1_enumset1(X3,X3,X3) = k4_xboole_0(k1_enumset1(X3,X3,X3),X4) ) ),
    inference(resolution,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f54,f50])).

fof(f43,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f42,f54,f50])).

fof(f42,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:42:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (12326)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (12338)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (12330)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (12327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (12324)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (12345)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (12337)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.55  % (12331)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.55  % (12328)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.55  % (12346)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.55  % (12331)Refutation not found, incomplete strategy% (12331)------------------------------
% 1.44/0.55  % (12331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (12331)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (12331)Memory used [KB]: 10618
% 1.44/0.55  % (12331)Time elapsed: 0.140 s
% 1.44/0.55  % (12331)------------------------------
% 1.44/0.55  % (12331)------------------------------
% 1.44/0.55  % (12323)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.56  % (12348)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.56  % (12325)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.56  % (12326)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f103,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f57,f58,f86,f102])).
% 1.44/0.56  fof(f102,plain,(
% 1.44/0.56    ~spl3_1 | ~spl3_2),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f101])).
% 1.44/0.56  fof(f101,plain,(
% 1.44/0.56    $false | (~spl3_1 | ~spl3_2)),
% 1.44/0.56    inference(subsumption_resolution,[],[f98,f51])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl3_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    spl3_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl3_2),
% 1.44/0.56    inference(superposition,[],[f48,f92])).
% 1.44/0.56  fof(f92,plain,(
% 1.44/0.56    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | ~spl3_2),
% 1.44/0.56    inference(resolution,[],[f89,f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(nnf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | ~spl3_2),
% 1.44/0.56    inference(subsumption_resolution,[],[f88,f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    v1_relat_1(sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 1.44/0.56    inference(flattening,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,plain,(
% 1.44/0.56    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.44/0.56    inference(negated_conjecture,[],[f8])).
% 1.44/0.56  fof(f8,conjecture,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 1.44/0.56  fof(f88,plain,(
% 1.44/0.56    r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 1.44/0.56    inference(trivial_inequality_removal,[],[f87])).
% 1.44/0.56  fof(f87,plain,(
% 1.44/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 1.44/0.56    inference(superposition,[],[f33,f56])).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl3_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f54])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    spl3_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(nnf_transformation,[],[f13])).
% 1.44/0.56  fof(f13,plain,(
% 1.44/0.56    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.44/0.56    inference(equality_resolution,[],[f46])).
% 1.44/0.56  % (12333)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f39,f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f28,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.44/0.56    inference(flattening,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.44/0.56    inference(nnf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    spl3_1 | spl3_2),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f85])).
% 1.44/0.56  fof(f85,plain,(
% 1.44/0.56    $false | (spl3_1 | spl3_2)),
% 1.44/0.56    inference(subsumption_resolution,[],[f84,f25])).
% 1.44/0.56  fof(f84,plain,(
% 1.44/0.56    ~v1_relat_1(sK1) | (spl3_1 | spl3_2)),
% 1.44/0.56    inference(subsumption_resolution,[],[f81,f55])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    k1_xboole_0 != k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | spl3_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f54])).
% 1.44/0.56  fof(f81,plain,(
% 1.44/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl3_1),
% 1.44/0.56    inference(resolution,[],[f80,f34])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f21])).
% 1.44/0.56  fof(f80,plain,(
% 1.44/0.56    r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | spl3_1),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f78])).
% 1.44/0.56  fof(f78,plain,(
% 1.44/0.56    r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | r1_xboole_0(k2_relat_1(sK1),k1_enumset1(sK0,sK0,sK0)) | spl3_1),
% 1.44/0.56    inference(resolution,[],[f75,f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f12,plain,(
% 1.44/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,plain,(
% 1.44/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(rectify,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.44/0.56  fof(f75,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(sK2(k2_relat_1(sK1),X0),k1_enumset1(sK0,sK0,sK0)) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | spl3_1),
% 1.44/0.56    inference(resolution,[],[f73,f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k1_enumset1(sK0,sK0,sK0))) ) | spl3_1),
% 1.44/0.56    inference(resolution,[],[f72,f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_relat_1(sK1)) | spl3_1),
% 1.44/0.56    inference(trivial_inequality_removal,[],[f71])).
% 1.44/0.56  fof(f71,plain,(
% 1.44/0.56    k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_relat_1(sK1)) | spl3_1),
% 1.44/0.56    inference(superposition,[],[f37,f67])).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_relat_1(sK1)) | spl3_1),
% 1.44/0.56    inference(resolution,[],[f60,f52])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f50])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X4,X3] : (r2_hidden(X3,X4) | k1_enumset1(X3,X3,X3) = k4_xboole_0(k1_enumset1(X3,X3,X3),X4)) )),
% 1.44/0.56    inference(resolution,[],[f44,f36])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.44/0.56    inference(definition_unfolding,[],[f35,f41])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    spl3_1 | ~spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f43,f54,f50])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    k1_xboole_0 != k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.44/0.56    inference(definition_unfolding,[],[f26,f41])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f57,plain,(
% 1.44/0.56    ~spl3_1 | spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f42,f54,f50])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.44/0.56    inference(definition_unfolding,[],[f27,f41])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (12326)------------------------------
% 1.44/0.56  % (12326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (12326)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (12326)Memory used [KB]: 10746
% 1.44/0.56  % (12326)Time elapsed: 0.135 s
% 1.44/0.56  % (12326)------------------------------
% 1.44/0.56  % (12326)------------------------------
% 1.44/0.56  % (12334)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.56  % (12325)Refutation not found, incomplete strategy% (12325)------------------------------
% 1.44/0.56  % (12325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (12325)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (12325)Memory used [KB]: 10618
% 1.44/0.56  % (12325)Time elapsed: 0.145 s
% 1.44/0.56  % (12325)------------------------------
% 1.44/0.56  % (12325)------------------------------
% 1.44/0.56  % (12339)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.56  % (12322)Success in time 0.194 s
%------------------------------------------------------------------------------
