%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:23 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 340 expanded)
%              Number of leaves         :   14 (  89 expanded)
%              Depth                    :   23
%              Number of atoms          :  244 (1535 expanded)
%              Number of equality atoms :   28 (  65 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f45])).

fof(f45,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f217,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f213,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f213,plain,(
    ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f212,f99])).

fof(f99,plain,(
    ! [X3] : ~ r1_tarski(k1_ordinal1(X3),X3) ),
    inference(subsumption_resolution,[],[f98,f49])).

fof(f49,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f98,plain,(
    ! [X3] :
      ( k1_ordinal1(X3) = X3
      | ~ r1_tarski(k1_ordinal1(X3),X3) ) ),
    inference(resolution,[],[f63,f81])).

fof(f81,plain,(
    ! [X0] : r1_tarski(X0,k1_ordinal1(X0)) ),
    inference(superposition,[],[f54,f51])).

fof(f51,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f212,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(forward_demodulation,[],[f211,f188])).

fof(f188,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f187,f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f127,f52])).

fof(f127,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | sK0 = sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f126,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f126,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f64,f101])).

fof(f101,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f46,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f187,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f186,f46])).

fof(f186,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f185,f45])).

fof(f185,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f173,f112])).

fof(f112,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X3,X2)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f59,f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f173,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f171,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f171,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f168,f63])).

fof(f168,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f167,f45])).

fof(f167,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f161,f52])).

fof(f161,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f93,f114])).

fof(f114,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f107,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_ordinal1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f69,f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f211,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f195,f79])).

fof(f79,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f67,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f195,plain,
    ( r2_hidden(sK0,sK0)
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(backward_demodulation,[],[f114,f188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:18:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (2152)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (2157)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (2157)Refutation not found, incomplete strategy% (2157)------------------------------
% 0.22/0.56  % (2157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (2149)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.57  % (2157)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (2157)Memory used [KB]: 10746
% 0.22/0.57  % (2157)Time elapsed: 0.138 s
% 0.22/0.57  % (2157)------------------------------
% 0.22/0.57  % (2157)------------------------------
% 0.22/0.57  % (2174)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (2173)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (2151)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.57  % (2159)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (2166)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.58  % (2153)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.58  % (2173)Refutation not found, incomplete strategy% (2173)------------------------------
% 1.37/0.58  % (2173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (2170)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.58  % (2173)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (2173)Memory used [KB]: 6268
% 1.37/0.58  % (2173)Time elapsed: 0.146 s
% 1.37/0.58  % (2173)------------------------------
% 1.37/0.58  % (2173)------------------------------
% 1.37/0.58  % (2150)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.58  % (2148)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.58  % (2162)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.58  % (2158)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.58  % (2156)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.58  % (2168)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.59  % (2147)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.37/0.59  % (2156)Refutation found. Thanks to Tanya!
% 1.37/0.59  % SZS status Theorem for theBenchmark
% 1.37/0.59  % SZS output start Proof for theBenchmark
% 1.37/0.59  fof(f218,plain,(
% 1.37/0.59    $false),
% 1.37/0.59    inference(subsumption_resolution,[],[f217,f45])).
% 1.37/0.59  fof(f45,plain,(
% 1.37/0.59    v3_ordinal1(sK0)),
% 1.37/0.59    inference(cnf_transformation,[],[f39])).
% 1.37/0.59  fof(f39,plain,(
% 1.37/0.59    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.37/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 1.37/0.59  fof(f37,plain,(
% 1.37/0.59    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.37/0.59    introduced(choice_axiom,[])).
% 1.37/0.59  fof(f38,plain,(
% 1.37/0.59    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 1.37/0.59    introduced(choice_axiom,[])).
% 1.37/0.59  fof(f36,plain,(
% 1.37/0.59    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.37/0.59    inference(flattening,[],[f35])).
% 1.37/0.59  fof(f35,plain,(
% 1.37/0.59    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.37/0.59    inference(nnf_transformation,[],[f24])).
% 1.37/0.59  fof(f24,plain,(
% 1.37/0.59    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.37/0.59    inference(ennf_transformation,[],[f22])).
% 1.37/0.59  fof(f22,negated_conjecture,(
% 1.37/0.59    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.37/0.59    inference(negated_conjecture,[],[f21])).
% 1.37/0.59  fof(f21,conjecture,(
% 1.37/0.59    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.37/0.59  fof(f217,plain,(
% 1.37/0.59    ~v3_ordinal1(sK0)),
% 1.37/0.59    inference(resolution,[],[f213,f52])).
% 1.37/0.59  fof(f52,plain,(
% 1.37/0.59    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f25])).
% 1.37/0.59  fof(f25,plain,(
% 1.37/0.59    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.37/0.59    inference(ennf_transformation,[],[f23])).
% 1.37/0.59  fof(f23,plain,(
% 1.37/0.59    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.37/0.59    inference(pure_predicate_removal,[],[f15])).
% 1.37/0.59  fof(f15,axiom,(
% 1.37/0.59    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).
% 1.37/0.59  fof(f213,plain,(
% 1.37/0.59    ~v3_ordinal1(k1_ordinal1(sK0))),
% 1.37/0.59    inference(subsumption_resolution,[],[f212,f99])).
% 1.37/0.59  fof(f99,plain,(
% 1.37/0.59    ( ! [X3] : (~r1_tarski(k1_ordinal1(X3),X3)) )),
% 1.37/0.59    inference(subsumption_resolution,[],[f98,f49])).
% 1.37/0.59  fof(f49,plain,(
% 1.37/0.59    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 1.37/0.59    inference(cnf_transformation,[],[f18])).
% 1.37/0.59  fof(f18,axiom,(
% 1.37/0.59    ! [X0] : k1_ordinal1(X0) != X0),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 1.37/0.59  fof(f98,plain,(
% 1.37/0.59    ( ! [X3] : (k1_ordinal1(X3) = X3 | ~r1_tarski(k1_ordinal1(X3),X3)) )),
% 1.37/0.59    inference(resolution,[],[f63,f81])).
% 1.37/0.59  fof(f81,plain,(
% 1.37/0.59    ( ! [X0] : (r1_tarski(X0,k1_ordinal1(X0))) )),
% 1.37/0.59    inference(superposition,[],[f54,f51])).
% 1.37/0.59  fof(f51,plain,(
% 1.37/0.59    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.37/0.59    inference(cnf_transformation,[],[f14])).
% 1.37/0.59  fof(f14,axiom,(
% 1.37/0.59    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.37/0.59  fof(f54,plain,(
% 1.37/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.37/0.59    inference(cnf_transformation,[],[f4])).
% 1.37/0.59  fof(f4,axiom,(
% 1.37/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.37/0.59  fof(f63,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f42])).
% 1.37/0.59  fof(f42,plain,(
% 1.37/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.59    inference(flattening,[],[f41])).
% 1.37/0.59  fof(f41,plain,(
% 1.37/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.59    inference(nnf_transformation,[],[f2])).
% 1.37/0.59  fof(f2,axiom,(
% 1.37/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.59  fof(f212,plain,(
% 1.37/0.59    r1_tarski(k1_ordinal1(sK0),sK0) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 1.37/0.59    inference(forward_demodulation,[],[f211,f188])).
% 1.37/0.59  fof(f188,plain,(
% 1.37/0.59    sK0 = sK1),
% 1.37/0.59    inference(subsumption_resolution,[],[f187,f129])).
% 1.37/0.59  fof(f129,plain,(
% 1.37/0.59    ~r2_hidden(sK0,sK1) | sK0 = sK1),
% 1.37/0.59    inference(subsumption_resolution,[],[f128,f45])).
% 1.37/0.59  fof(f128,plain,(
% 1.37/0.59    sK0 = sK1 | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 1.37/0.59    inference(resolution,[],[f127,f52])).
% 1.37/0.59  fof(f127,plain,(
% 1.37/0.59    ~v3_ordinal1(k1_ordinal1(sK0)) | sK0 = sK1 | ~r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(subsumption_resolution,[],[f126,f57])).
% 1.37/0.59  fof(f57,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f28])).
% 1.37/0.59  fof(f28,plain,(
% 1.37/0.59    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.37/0.59    inference(ennf_transformation,[],[f1])).
% 1.37/0.59  fof(f1,axiom,(
% 1.37/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.37/0.59  fof(f126,plain,(
% 1.37/0.59    r2_hidden(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(resolution,[],[f64,f101])).
% 1.37/0.59  fof(f101,plain,(
% 1.37/0.59    r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(subsumption_resolution,[],[f100,f46])).
% 1.37/0.59  fof(f46,plain,(
% 1.37/0.59    v3_ordinal1(sK1)),
% 1.37/0.59    inference(cnf_transformation,[],[f39])).
% 1.37/0.59  fof(f100,plain,(
% 1.37/0.59    r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(resolution,[],[f53,f48])).
% 1.37/0.59  fof(f48,plain,(
% 1.37/0.59    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(cnf_transformation,[],[f39])).
% 1.37/0.59  fof(f53,plain,(
% 1.37/0.59    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f27])).
% 1.37/0.59  fof(f27,plain,(
% 1.37/0.59    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.37/0.59    inference(flattening,[],[f26])).
% 1.37/0.59  fof(f26,plain,(
% 1.37/0.59    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.37/0.59    inference(ennf_transformation,[],[f19])).
% 1.37/0.59  fof(f19,axiom,(
% 1.37/0.59    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.37/0.59  fof(f64,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.37/0.59    inference(cnf_transformation,[],[f44])).
% 1.37/0.59  fof(f44,plain,(
% 1.37/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.37/0.59    inference(flattening,[],[f43])).
% 1.37/0.59  fof(f43,plain,(
% 1.37/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.37/0.59    inference(nnf_transformation,[],[f17])).
% 1.37/0.59  fof(f17,axiom,(
% 1.37/0.59    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.37/0.59  fof(f187,plain,(
% 1.37/0.59    sK0 = sK1 | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(subsumption_resolution,[],[f186,f46])).
% 1.37/0.59  fof(f186,plain,(
% 1.37/0.59    sK0 = sK1 | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(subsumption_resolution,[],[f185,f45])).
% 1.37/0.59  fof(f185,plain,(
% 1.37/0.59    sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(resolution,[],[f173,f112])).
% 1.37/0.59  fof(f112,plain,(
% 1.37/0.59    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X3,X2)) )),
% 1.37/0.59    inference(duplicate_literal_removal,[],[f109])).
% 1.37/0.59  fof(f109,plain,(
% 1.37/0.59    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X3,X2) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2)) )),
% 1.37/0.59    inference(resolution,[],[f59,f53])).
% 1.37/0.59  fof(f59,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f40])).
% 1.37/0.59  fof(f40,plain,(
% 1.37/0.59    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.37/0.59    inference(nnf_transformation,[],[f32])).
% 1.37/0.59  fof(f32,plain,(
% 1.37/0.59    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.37/0.59    inference(flattening,[],[f31])).
% 1.37/0.59  fof(f31,plain,(
% 1.37/0.59    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.37/0.59    inference(ennf_transformation,[],[f16])).
% 1.37/0.59  fof(f16,axiom,(
% 1.37/0.59    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.37/0.59  fof(f173,plain,(
% 1.37/0.59    ~r1_tarski(sK1,sK0) | sK0 = sK1),
% 1.37/0.59    inference(subsumption_resolution,[],[f171,f67])).
% 1.37/0.59  fof(f67,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f33])).
% 1.37/0.59  fof(f33,plain,(
% 1.37/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.37/0.59    inference(ennf_transformation,[],[f20])).
% 1.37/0.59  fof(f20,axiom,(
% 1.37/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.37/0.59  fof(f171,plain,(
% 1.37/0.59    r2_hidden(sK0,sK1) | sK0 = sK1 | ~r1_tarski(sK1,sK0)),
% 1.37/0.59    inference(resolution,[],[f168,f63])).
% 1.37/0.59  fof(f168,plain,(
% 1.37/0.59    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(subsumption_resolution,[],[f167,f45])).
% 1.37/0.59  fof(f167,plain,(
% 1.37/0.59    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 1.37/0.59    inference(resolution,[],[f161,f52])).
% 1.37/0.59  fof(f161,plain,(
% 1.37/0.59    ~v3_ordinal1(k1_ordinal1(sK0)) | r1_tarski(sK0,sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(resolution,[],[f93,f114])).
% 1.37/0.59  fof(f114,plain,(
% 1.37/0.59    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(subsumption_resolution,[],[f107,f46])).
% 1.37/0.59  fof(f107,plain,(
% 1.37/0.59    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(resolution,[],[f59,f47])).
% 1.37/0.59  fof(f47,plain,(
% 1.37/0.59    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.37/0.59    inference(cnf_transformation,[],[f39])).
% 1.37/0.59  fof(f93,plain,(
% 1.37/0.59    ( ! [X0,X1] : (~r1_tarski(k1_ordinal1(X0),X1) | r1_tarski(X0,X1)) )),
% 1.37/0.59    inference(superposition,[],[f69,f51])).
% 1.37/0.59  fof(f69,plain,(
% 1.37/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.37/0.59    inference(cnf_transformation,[],[f34])).
% 1.37/0.59  fof(f34,plain,(
% 1.37/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.37/0.59    inference(ennf_transformation,[],[f3])).
% 1.37/0.59  fof(f3,axiom,(
% 1.37/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.37/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.37/0.59  fof(f211,plain,(
% 1.37/0.59    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 1.37/0.59    inference(subsumption_resolution,[],[f195,f79])).
% 1.37/0.59  fof(f79,plain,(
% 1.37/0.59    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 1.37/0.59    inference(resolution,[],[f67,f74])).
% 1.37/0.59  fof(f74,plain,(
% 1.37/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.37/0.59    inference(equality_resolution,[],[f62])).
% 1.37/0.59  fof(f62,plain,(
% 1.37/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.37/0.59    inference(cnf_transformation,[],[f42])).
% 1.37/0.59  fof(f195,plain,(
% 1.37/0.59    r2_hidden(sK0,sK0) | r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 1.37/0.59    inference(backward_demodulation,[],[f114,f188])).
% 1.37/0.59  % SZS output end Proof for theBenchmark
% 1.37/0.59  % (2156)------------------------------
% 1.37/0.59  % (2156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.59  % (2156)Termination reason: Refutation
% 1.37/0.59  
% 1.37/0.59  % (2156)Memory used [KB]: 1791
% 1.37/0.59  % (2156)Time elapsed: 0.155 s
% 1.37/0.59  % (2156)------------------------------
% 1.37/0.59  % (2156)------------------------------
% 1.37/0.59  % (2161)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.59  % (2167)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.59  % (2169)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.59  % (2154)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.76/0.59  % (2176)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.76/0.60  % (2160)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.76/0.60  % (2175)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.76/0.60  % (2155)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.76/0.60  % (2172)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.76/0.60  % (2163)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.76/0.60  % (2148)Refutation not found, incomplete strategy% (2148)------------------------------
% 1.76/0.60  % (2148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (2148)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (2148)Memory used [KB]: 1663
% 1.76/0.60  % (2148)Time elapsed: 0.174 s
% 1.76/0.60  % (2148)------------------------------
% 1.76/0.60  % (2148)------------------------------
% 1.76/0.60  % (2176)Refutation not found, incomplete strategy% (2176)------------------------------
% 1.76/0.60  % (2176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (2176)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (2176)Memory used [KB]: 1663
% 1.76/0.60  % (2176)Time elapsed: 0.165 s
% 1.76/0.60  % (2176)------------------------------
% 1.76/0.60  % (2176)------------------------------
% 1.76/0.60  % (2163)Refutation not found, incomplete strategy% (2163)------------------------------
% 1.76/0.60  % (2163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (2163)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (2163)Memory used [KB]: 10618
% 1.76/0.60  % (2163)Time elapsed: 0.179 s
% 1.76/0.60  % (2163)------------------------------
% 1.76/0.60  % (2163)------------------------------
% 1.76/0.61  % (2165)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.76/0.61  % (2146)Success in time 0.237 s
%------------------------------------------------------------------------------
