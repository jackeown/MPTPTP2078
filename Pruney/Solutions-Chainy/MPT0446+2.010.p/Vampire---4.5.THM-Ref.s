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
% DateTime   : Thu Dec  3 12:47:07 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 186 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 453 expanded)
%              Number of equality atoms :   24 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f94,f158])).

fof(f158,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f78,f153])).

fof(f153,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl4_2 ),
    inference(resolution,[],[f148,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK2))
        | ~ r2_hidden(sK1,X0) )
    | spl4_2 ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f69,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_2
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f148,plain,(
    r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f143,f35])).

fof(f35,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f143,plain,(
    r1_tarski(k2_relat_1(sK2),k3_tarski(k1_zfmisc_1(k3_relat_1(sK2)))) ),
    inference(resolution,[],[f125,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f125,plain,(
    r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(k3_relat_1(sK2))) ),
    inference(resolution,[],[f87,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f87,plain,(
    r1_tarski(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k3_relat_1(sK2))) ),
    inference(superposition,[],[f36,f71])).

fof(f71,plain,(
    k3_relat_1(sK2) = k3_tarski(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f32,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r2_hidden(sK1,k3_relat_1(sK2))
      | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
    & r2_hidden(k4_tarski(sK0,sK1),sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k3_relat_1(X2))
          | ~ r2_hidden(X0,k3_relat_1(X2)) )
        & r2_hidden(k4_tarski(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k3_relat_1(sK2))
        | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
      & r2_hidden(k4_tarski(sK0,sK1),sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f36,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f78,plain,(
    r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(global_subsumption,[],[f32,f76])).

fof(f76,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f33,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f77,f88])).

fof(f88,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl4_1 ),
    inference(resolution,[],[f86,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK2))
        | ~ r2_hidden(sK0,X0) )
    | spl4_1 ),
    inference(resolution,[],[f66,f42])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,(
    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) ),
    inference(superposition,[],[f60,f71])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f77,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(global_subsumption,[],[f32,f75])).

fof(f75,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f68,f65])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.28/0.54  % (15767)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.55  % (15774)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (15766)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.56  % (15767)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f159,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(avatar_sat_refutation,[],[f70,f94,f158])).
% 1.50/0.56  fof(f158,plain,(
% 1.50/0.56    spl4_2),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f156])).
% 1.50/0.56  fof(f156,plain,(
% 1.50/0.56    $false | spl4_2),
% 1.50/0.56    inference(subsumption_resolution,[],[f78,f153])).
% 1.50/0.56  fof(f153,plain,(
% 1.50/0.56    ~r2_hidden(sK1,k2_relat_1(sK2)) | spl4_2),
% 1.50/0.56    inference(resolution,[],[f148,f95])).
% 1.50/0.56  fof(f95,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | ~r2_hidden(sK1,X0)) ) | spl4_2),
% 1.50/0.56    inference(resolution,[],[f69,f42])).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.56    inference(rectify,[],[f26])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.56    inference(nnf_transformation,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.56  fof(f69,plain,(
% 1.50/0.56    ~r2_hidden(sK1,k3_relat_1(sK2)) | spl4_2),
% 1.50/0.56    inference(avatar_component_clause,[],[f68])).
% 1.50/0.56  fof(f68,plain,(
% 1.50/0.56    spl4_2 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.50/0.56  fof(f148,plain,(
% 1.50/0.56    r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2))),
% 1.50/0.56    inference(forward_demodulation,[],[f143,f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,axiom,(
% 1.50/0.56    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.50/0.56  fof(f143,plain,(
% 1.50/0.56    r1_tarski(k2_relat_1(sK2),k3_tarski(k1_zfmisc_1(k3_relat_1(sK2))))),
% 1.50/0.56    inference(resolution,[],[f125,f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.50/0.56  fof(f125,plain,(
% 1.50/0.56    r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(k3_relat_1(sK2)))),
% 1.50/0.56    inference(resolution,[],[f87,f62])).
% 1.50/0.56  fof(f62,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f49,f57])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f40,f56])).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f45,f55])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f51,f54])).
% 1.50/0.56  fof(f54,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f52,f53])).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.50/0.56  fof(f52,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.56  fof(f51,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.56    inference(flattening,[],[f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.56    inference(nnf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.50/0.56  fof(f87,plain,(
% 1.50/0.56    r1_tarski(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)),k1_zfmisc_1(k3_relat_1(sK2)))),
% 1.50/0.56    inference(superposition,[],[f36,f71])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    k3_relat_1(sK2) = k3_tarski(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.50/0.56    inference(resolution,[],[f32,f59])).
% 1.50/0.56  fof(f59,plain,(
% 1.50/0.56    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f37,f58])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f39,f57])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f13])).
% 1.50/0.56  fof(f13,axiom,(
% 1.50/0.56    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    v1_relat_1(sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    (~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2))) & r2_hidden(k4_tarski(sK0,sK1),sK2) & v1_relat_1(sK2)),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2)) => ((~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2))) & r2_hidden(k4_tarski(sK0,sK1),sK2) & v1_relat_1(sK2))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f18,plain,(
% 1.50/0.56    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 1.50/0.56    inference(flattening,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 1.50/0.56    inference(ennf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.50/0.56    inference(negated_conjecture,[],[f15])).
% 1.50/0.56  fof(f15,conjecture,(
% 1.50/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.50/0.56  fof(f78,plain,(
% 1.50/0.56    r2_hidden(sK1,k2_relat_1(sK2))),
% 1.50/0.56    inference(global_subsumption,[],[f32,f76])).
% 1.50/0.56  fof(f76,plain,(
% 1.50/0.56    r2_hidden(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.50/0.56    inference(resolution,[],[f33,f47])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.50/0.56    inference(flattening,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.50/0.56    inference(ennf_transformation,[],[f14])).
% 1.50/0.56  fof(f14,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    spl4_1),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f92])).
% 1.50/0.56  fof(f92,plain,(
% 1.50/0.56    $false | spl4_1),
% 1.50/0.56    inference(subsumption_resolution,[],[f77,f88])).
% 1.50/0.56  fof(f88,plain,(
% 1.50/0.56    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl4_1),
% 1.50/0.56    inference(resolution,[],[f86,f72])).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | ~r2_hidden(sK0,X0)) ) | spl4_1),
% 1.50/0.56    inference(resolution,[],[f66,f42])).
% 1.50/0.56  fof(f66,plain,(
% 1.50/0.56    ~r2_hidden(sK0,k3_relat_1(sK2)) | spl4_1),
% 1.50/0.56    inference(avatar_component_clause,[],[f65])).
% 1.50/0.56  fof(f65,plain,(
% 1.50/0.56    spl4_1 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.50/0.56  fof(f86,plain,(
% 1.50/0.56    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2))),
% 1.50/0.56    inference(superposition,[],[f60,f71])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f38,f58])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.56  fof(f77,plain,(
% 1.50/0.56    r2_hidden(sK0,k1_relat_1(sK2))),
% 1.50/0.56    inference(global_subsumption,[],[f32,f75])).
% 1.50/0.56  fof(f75,plain,(
% 1.50/0.56    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.50/0.56    inference(resolution,[],[f33,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f23])).
% 1.50/0.56  fof(f70,plain,(
% 1.50/0.56    ~spl4_1 | ~spl4_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f34,f68,f65])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2))),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (15767)------------------------------
% 1.50/0.56  % (15767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (15767)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (15767)Memory used [KB]: 10746
% 1.50/0.56  % (15767)Time elapsed: 0.136 s
% 1.50/0.56  % (15767)------------------------------
% 1.50/0.56  % (15767)------------------------------
% 1.50/0.56  % (15764)Success in time 0.193 s
%------------------------------------------------------------------------------
