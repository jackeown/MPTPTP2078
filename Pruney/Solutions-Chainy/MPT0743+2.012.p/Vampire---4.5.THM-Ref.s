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
% DateTime   : Thu Dec  3 12:55:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 653 expanded)
%              Number of leaves         :   12 ( 168 expanded)
%              Depth                    :   29
%              Number of atoms          :  311 (2343 expanded)
%              Number of equality atoms :   45 ( 322 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(resolution,[],[f224,f32])).

fof(f32,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f224,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f218,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f52,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f42,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f218,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f217,f60])).

fof(f60,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f217,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(resolution,[],[f209,f64])).

fof(f64,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f209,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f208,f181])).

fof(f181,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f178,f32])).

fof(f178,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f173,f33])).

fof(f33,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f173,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f167,f144])).

% (13499)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f144,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f137,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f137,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f134,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f134,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f107,f115])).

fof(f115,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f114,f58])).

fof(f114,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f88,f78])).

fof(f78,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f35,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | X0 = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f74,f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f167,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f157,f58])).

fof(f157,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f120,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f120,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f115,f93])).

fof(f93,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X4,X5] :
      ( ~ r1_ordinal1(X4,X5)
      | ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(X4)
      | ~ r2_hidden(X5,X4) ) ),
    inference(resolution,[],[f36,f45])).

fof(f208,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(forward_demodulation,[],[f187,f181])).

fof(f187,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(backward_demodulation,[],[f93,f181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (13500)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.48  % (13528)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (13519)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.48  % (13509)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (13502)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (13521)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (13502)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (13513)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (13520)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (13508)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (13511)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(resolution,[],[f224,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    v3_ordinal1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    ~v3_ordinal1(sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f223])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0)),
% 0.20/0.50    inference(resolution,[],[f218,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f42,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f43,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f217,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | X0 != X1) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f52])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 0.20/0.51    inference(resolution,[],[f209,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f45,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    r2_hidden(sK0,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f208,f181])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    sK0 = sK1),
% 0.20/0.51    inference(resolution,[],[f178,f32])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.20/0.51    inference(resolution,[],[f173,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    v3_ordinal1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1),
% 0.20/0.51    inference(resolution,[],[f167,f144])).
% 0.20/0.51  % (13499)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f137,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f134,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f107,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f114,f58])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK0 = sK1),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    sK0 = sK1 | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f88,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f38,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ~r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f52])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | X0 = X1 | ~r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f57,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f39,f52])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.20/0.51    inference(resolution,[],[f74,f38])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.51    inference(resolution,[],[f36,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f166])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ~v3_ordinal1(sK0) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.20/0.51    inference(resolution,[],[f157,f58])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK0) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f120,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f52])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(resolution,[],[f115,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(resolution,[],[f76,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(definition_unfolding,[],[f34,f52])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X4,X5] : (~r1_ordinal1(X4,X5) | ~v3_ordinal1(X5) | ~v3_ordinal1(X4) | ~r2_hidden(X5,X4)) )),
% 0.20/0.51    inference(resolution,[],[f36,f45])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | r2_hidden(sK0,sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(forward_demodulation,[],[f187,f181])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    r2_hidden(sK0,sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(backward_demodulation,[],[f93,f181])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13502)------------------------------
% 0.20/0.51  % (13502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13502)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13502)Memory used [KB]: 1791
% 0.20/0.51  % (13502)Time elapsed: 0.088 s
% 0.20/0.51  % (13502)------------------------------
% 0.20/0.51  % (13502)------------------------------
% 0.20/0.51  % (13494)Success in time 0.154 s
%------------------------------------------------------------------------------
