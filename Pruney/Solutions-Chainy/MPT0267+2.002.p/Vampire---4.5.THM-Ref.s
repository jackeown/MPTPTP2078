%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:34 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 279 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  220 ( 478 expanded)
%              Number of equality atoms :   47 ( 187 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f85,f199,f211,f215,f369,f380,f390,f395])).

fof(f395,plain,
    ( ~ spl6_1
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f212,f368])).

fof(f368,plain,
    ( r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl6_6
  <=> r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f212,plain,
    ( ~ r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f74,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f74,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f390,plain,
    ( spl6_2
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f78,f368,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f57])).

% (19275)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f78,plain,
    ( sK0 != sK2
    | spl6_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f380,plain,
    ( ~ spl6_4
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f220,f364])).

fof(f364,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl6_5
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f220,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f218,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f218,plain,
    ( ~ r1_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f198,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f34,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f198,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f369,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f358,f196,f366,f362])).

fof(f358,plain,
    ( r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(superposition,[],[f198,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f57,f57])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f215,plain,
    ( spl6_4
    | spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f214,f72,f81,f196])).

fof(f81,plain,
    ( spl6_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f214,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl6_1 ),
    inference(resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f211,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f70,f120,f202,f36])).

fof(f202,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f74,f77])).

fof(f77,plain,
    ( sK0 = sK2
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f120,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[],[f116,f61])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f35,f90])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2] : r2_hidden(X2,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f199,plain,
    ( spl6_4
    | ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f193,f72,f81,f196])).

fof(f193,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl6_1 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f85,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f60,f81,f76,f72])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f26,f33,f57])).

fof(f26,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f84,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f59,f81,f72])).

fof(f59,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f27,f33,f57])).

fof(f27,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f58,f76,f72])).

fof(f58,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f28,f33,f57])).

fof(f28,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:43:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.21/0.51  % (19251)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (19249)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (19248)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (19273)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (19269)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (19257)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (19247)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.54  % (19264)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.54  % (19270)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.54  % (19259)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.54  % (19262)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.54  % (19255)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.54  % (19260)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.54  % (19250)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (19252)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.54  % (19253)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.55  % (19256)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.55  % (19267)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (19271)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.55  % (19276)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.55  % (19274)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.55  % (19265)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.56  % (19263)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.56  % (19272)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.56  % (19263)Refutation not found, incomplete strategy% (19263)------------------------------
% 1.32/0.56  % (19263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (19263)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (19263)Memory used [KB]: 10618
% 1.32/0.56  % (19263)Time elapsed: 0.140 s
% 1.32/0.56  % (19263)------------------------------
% 1.32/0.56  % (19263)------------------------------
% 1.48/0.56  % (19268)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.56  % (19258)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.56  % (19266)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.56  % (19260)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.57  % (19254)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.57  % (19261)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.58  % SZS output start Proof for theBenchmark
% 1.48/0.58  fof(f396,plain,(
% 1.48/0.58    $false),
% 1.48/0.58    inference(avatar_sat_refutation,[],[f79,f84,f85,f199,f211,f215,f369,f380,f390,f395])).
% 1.48/0.58  fof(f395,plain,(
% 1.48/0.58    ~spl6_1 | ~spl6_6),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f381])).
% 1.48/0.58  fof(f381,plain,(
% 1.48/0.58    $false | (~spl6_1 | ~spl6_6)),
% 1.48/0.58    inference(subsumption_resolution,[],[f212,f368])).
% 1.48/0.58  fof(f368,plain,(
% 1.48/0.58    r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl6_6),
% 1.48/0.58    inference(avatar_component_clause,[],[f366])).
% 1.48/0.58  fof(f366,plain,(
% 1.48/0.58    spl6_6 <=> r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.48/0.58  fof(f212,plain,(
% 1.48/0.58    ~r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl6_1),
% 1.48/0.58    inference(resolution,[],[f74,f94])).
% 1.48/0.58  fof(f94,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r2_hidden(X0,X1)) )),
% 1.48/0.58    inference(resolution,[],[f36,f61])).
% 1.48/0.58  fof(f61,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f30,f33])).
% 1.48/0.58  fof(f33,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f5])).
% 1.48/0.58  fof(f5,axiom,(
% 1.48/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.58  fof(f30,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f6])).
% 1.48/0.58  fof(f6,axiom,(
% 1.48/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.48/0.58  fof(f36,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f22])).
% 1.48/0.58  fof(f22,plain,(
% 1.48/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f19])).
% 1.48/0.58  fof(f19,plain,(
% 1.48/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(rectify,[],[f3])).
% 1.48/0.58  fof(f3,axiom,(
% 1.48/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.48/0.58  fof(f74,plain,(
% 1.48/0.58    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl6_1),
% 1.48/0.58    inference(avatar_component_clause,[],[f72])).
% 1.48/0.58  fof(f72,plain,(
% 1.48/0.58    spl6_1 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.48/0.58  fof(f390,plain,(
% 1.48/0.58    spl6_2 | ~spl6_6),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f382])).
% 1.48/0.58  fof(f382,plain,(
% 1.48/0.58    $false | (spl6_2 | ~spl6_6)),
% 1.48/0.58    inference(unit_resulting_resolution,[],[f78,f368,f68])).
% 1.48/0.58  fof(f68,plain,(
% 1.48/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.48/0.58    inference(equality_resolution,[],[f66])).
% 1.48/0.58  fof(f66,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.48/0.58    inference(definition_unfolding,[],[f42,f57])).
% 1.48/0.58  % (19275)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.58  fof(f57,plain,(
% 1.48/0.58    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f29,f56])).
% 1.48/0.58  fof(f56,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f32,f55])).
% 1.48/0.58  fof(f55,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f45,f54])).
% 1.48/0.58  fof(f54,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f50,f53])).
% 1.48/0.58  fof(f53,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f51,f52])).
% 1.48/0.58  fof(f52,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f13])).
% 1.48/0.58  fof(f13,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.48/0.58  fof(f51,plain,(
% 1.48/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f12])).
% 1.48/0.58  fof(f12,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.58  fof(f50,plain,(
% 1.48/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f11])).
% 1.48/0.58  fof(f11,axiom,(
% 1.48/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.58  fof(f45,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f10])).
% 1.48/0.58  fof(f10,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.58  fof(f32,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f9])).
% 1.48/0.58  fof(f9,axiom,(
% 1.48/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.58  fof(f29,plain,(
% 1.48/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f8])).
% 1.48/0.58  fof(f8,axiom,(
% 1.48/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.58  fof(f42,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.48/0.58    inference(cnf_transformation,[],[f7])).
% 1.48/0.58  fof(f7,axiom,(
% 1.48/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.48/0.58  fof(f78,plain,(
% 1.48/0.58    sK0 != sK2 | spl6_2),
% 1.48/0.58    inference(avatar_component_clause,[],[f76])).
% 1.48/0.58  fof(f76,plain,(
% 1.48/0.58    spl6_2 <=> sK0 = sK2),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.48/0.58  fof(f380,plain,(
% 1.48/0.58    ~spl6_4 | spl6_5),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f375])).
% 1.48/0.58  fof(f375,plain,(
% 1.48/0.58    $false | (~spl6_4 | spl6_5)),
% 1.48/0.58    inference(subsumption_resolution,[],[f220,f364])).
% 1.48/0.58  fof(f364,plain,(
% 1.48/0.58    ~r2_hidden(sK2,sK1) | spl6_5),
% 1.48/0.58    inference(avatar_component_clause,[],[f362])).
% 1.48/0.58  fof(f362,plain,(
% 1.48/0.58    spl6_5 <=> r2_hidden(sK2,sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.48/0.58  fof(f220,plain,(
% 1.48/0.58    r2_hidden(sK2,sK1) | ~spl6_4),
% 1.48/0.58    inference(resolution,[],[f218,f62])).
% 1.48/0.58  fof(f62,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f39,f57])).
% 1.48/0.58  fof(f39,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f23])).
% 1.48/0.58  fof(f23,plain,(
% 1.48/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.48/0.58    inference(ennf_transformation,[],[f14])).
% 1.48/0.58  fof(f14,axiom,(
% 1.48/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.48/0.58  fof(f218,plain,(
% 1.48/0.58    ~r1_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) | ~spl6_4),
% 1.48/0.58    inference(resolution,[],[f198,f90])).
% 1.48/0.58  fof(f90,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(superposition,[],[f34,f31])).
% 1.48/0.58  fof(f31,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f1])).
% 1.48/0.58  fof(f1,axiom,(
% 1.48/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.48/0.58  fof(f34,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f21])).
% 1.48/0.58  fof(f21,plain,(
% 1.48/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f18])).
% 1.48/0.58  fof(f18,plain,(
% 1.48/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.58    inference(rectify,[],[f4])).
% 1.48/0.58  fof(f4,axiom,(
% 1.48/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.48/0.58  fof(f198,plain,(
% 1.48/0.58    r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl6_4),
% 1.48/0.58    inference(avatar_component_clause,[],[f196])).
% 1.48/0.58  fof(f196,plain,(
% 1.48/0.58    spl6_4 <=> r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.48/0.58  fof(f369,plain,(
% 1.48/0.58    ~spl6_5 | spl6_6 | ~spl6_4),
% 1.48/0.58    inference(avatar_split_clause,[],[f358,f196,f366,f362])).
% 1.48/0.58  fof(f358,plain,(
% 1.48/0.58    r2_hidden(sK0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(sK2,sK1) | ~spl6_4),
% 1.48/0.58    inference(superposition,[],[f198,f63])).
% 1.48/0.58  fof(f63,plain,(
% 1.48/0.58    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.48/0.58    inference(definition_unfolding,[],[f40,f57,f57])).
% 1.48/0.58  fof(f40,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 1.48/0.58    inference(cnf_transformation,[],[f24])).
% 1.48/0.58  fof(f24,plain,(
% 1.48/0.58    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.48/0.58    inference(ennf_transformation,[],[f15])).
% 1.48/0.58  fof(f15,axiom,(
% 1.48/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.48/0.58  fof(f215,plain,(
% 1.48/0.58    spl6_4 | spl6_3 | ~spl6_1),
% 1.48/0.58    inference(avatar_split_clause,[],[f214,f72,f81,f196])).
% 1.48/0.58  fof(f81,plain,(
% 1.48/0.58    spl6_3 <=> r2_hidden(sK0,sK1)),
% 1.48/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.48/0.58  fof(f214,plain,(
% 1.48/0.58    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl6_1),
% 1.48/0.58    inference(resolution,[],[f74,f46])).
% 1.48/0.58  fof(f46,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f25])).
% 1.48/0.58  fof(f25,plain,(
% 1.48/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.48/0.58    inference(ennf_transformation,[],[f2])).
% 1.48/0.58  fof(f2,axiom,(
% 1.48/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.48/0.58  fof(f211,plain,(
% 1.48/0.58    ~spl6_1 | ~spl6_2),
% 1.48/0.58    inference(avatar_contradiction_clause,[],[f205])).
% 1.48/0.58  fof(f205,plain,(
% 1.48/0.58    $false | (~spl6_1 | ~spl6_2)),
% 1.48/0.58    inference(unit_resulting_resolution,[],[f70,f120,f202,f36])).
% 1.48/0.58  fof(f202,plain,(
% 1.48/0.58    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl6_1 | ~spl6_2)),
% 1.48/0.58    inference(forward_demodulation,[],[f74,f77])).
% 1.48/0.58  fof(f77,plain,(
% 1.48/0.58    sK0 = sK2 | ~spl6_2),
% 1.48/0.58    inference(avatar_component_clause,[],[f76])).
% 1.48/0.58  fof(f120,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.48/0.58    inference(resolution,[],[f116,f61])).
% 1.48/0.58  fof(f116,plain,(
% 1.48/0.58    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(resolution,[],[f35,f90])).
% 1.48/0.58  fof(f35,plain,(
% 1.48/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f21])).
% 1.48/0.58  fof(f70,plain,(
% 1.48/0.58    ( ! [X2] : (r2_hidden(X2,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) )),
% 1.48/0.58    inference(equality_resolution,[],[f69])).
% 1.48/0.58  fof(f69,plain,(
% 1.48/0.58    ( ! [X2,X1] : (r2_hidden(X2,X1) | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X1) )),
% 1.48/0.58    inference(equality_resolution,[],[f67])).
% 1.48/0.58  fof(f67,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.48/0.58    inference(definition_unfolding,[],[f41,f57])).
% 1.48/0.58  fof(f41,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.48/0.58    inference(cnf_transformation,[],[f7])).
% 1.48/0.58  fof(f199,plain,(
% 1.48/0.58    spl6_4 | ~spl6_3 | spl6_1),
% 1.48/0.58    inference(avatar_split_clause,[],[f193,f72,f81,f196])).
% 1.48/0.58  fof(f193,plain,(
% 1.48/0.58    ~r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl6_1),
% 1.48/0.58    inference(resolution,[],[f73,f49])).
% 1.48/0.58  fof(f49,plain,(
% 1.48/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f25])).
% 1.48/0.58  fof(f73,plain,(
% 1.48/0.58    ~r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | spl6_1),
% 1.48/0.58    inference(avatar_component_clause,[],[f72])).
% 1.48/0.58  fof(f85,plain,(
% 1.48/0.58    ~spl6_1 | spl6_2 | ~spl6_3),
% 1.48/0.58    inference(avatar_split_clause,[],[f60,f81,f76,f72])).
% 1.48/0.58  fof(f60,plain,(
% 1.48/0.58    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.48/0.58    inference(definition_unfolding,[],[f26,f33,f57])).
% 1.48/0.58  fof(f26,plain,(
% 1.48/0.58    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.48/0.58    inference(cnf_transformation,[],[f20])).
% 1.48/0.58  fof(f20,plain,(
% 1.48/0.58    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.48/0.58    inference(ennf_transformation,[],[f17])).
% 1.48/0.58  fof(f17,negated_conjecture,(
% 1.48/0.58    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.48/0.58    inference(negated_conjecture,[],[f16])).
% 1.48/0.58  fof(f16,conjecture,(
% 1.48/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.48/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.48/0.58  fof(f84,plain,(
% 1.48/0.58    spl6_1 | spl6_3),
% 1.48/0.58    inference(avatar_split_clause,[],[f59,f81,f72])).
% 1.48/0.58  fof(f59,plain,(
% 1.48/0.58    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.48/0.58    inference(definition_unfolding,[],[f27,f33,f57])).
% 1.48/0.58  fof(f27,plain,(
% 1.48/0.58    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.48/0.58    inference(cnf_transformation,[],[f20])).
% 1.48/0.58  fof(f79,plain,(
% 1.48/0.58    spl6_1 | ~spl6_2),
% 1.48/0.58    inference(avatar_split_clause,[],[f58,f76,f72])).
% 1.48/0.58  fof(f58,plain,(
% 1.48/0.58    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.48/0.58    inference(definition_unfolding,[],[f28,f33,f57])).
% 1.48/0.58  fof(f28,plain,(
% 1.48/0.58    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.48/0.58    inference(cnf_transformation,[],[f20])).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (19260)------------------------------
% 1.48/0.58  % (19260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (19260)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (19260)Memory used [KB]: 6396
% 1.48/0.58  % (19260)Time elapsed: 0.152 s
% 1.48/0.58  % (19260)------------------------------
% 1.48/0.58  % (19260)------------------------------
% 1.48/0.58  % (19244)Success in time 0.208 s
%------------------------------------------------------------------------------
