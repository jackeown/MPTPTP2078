%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 498 expanded)
%              Number of leaves         :   12 ( 137 expanded)
%              Depth                    :   22
%              Number of atoms          :  244 (2115 expanded)
%              Number of equality atoms :   27 ( 141 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f212,f127])).

fof(f127,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X7)
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f66,f83])).

fof(f83,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_tarski(X0,X1),X0) ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f82,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f64,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f212,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f211,f189])).

fof(f189,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f188,f104])).

fof(f104,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f103,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f67,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

% (28713)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f103,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f101,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f101,plain,
    ( r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f100,f40])).

fof(f40,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f100,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f41,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f99,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f43,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f188,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f178,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f178,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | sK0 = sK1 ),
    inference(resolution,[],[f121,f141])).

fof(f141,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f139,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f139,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f138,f104])).

fof(f138,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f109,f41])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK0)
      | r2_hidden(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f108,f40])).

fof(f108,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | ~ v3_ordinal1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | ~ v3_ordinal1(sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f105,f46])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f121,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(resolution,[],[f119,f69])).

fof(f69,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f42,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f106,f40])).

fof(f106,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(X1,sK1)
      | ~ r1_ordinal1(X1,sK1) ) ),
    inference(resolution,[],[f49,f41])).

fof(f211,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f193,f75])).

fof(f75,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f193,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f101,f189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (28725)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (28736)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (28726)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (28733)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (28717)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (28728)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (28718)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (28720)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (28733)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (28734)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (28714)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (28723)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f212,f127])).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    ( ! [X6,X7] : (~r2_hidden(X7,X7) | ~r2_hidden(X6,X7)) )),
% 0.21/0.57    inference(resolution,[],[f66,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X0)) )),
% 0.21/0.57    inference(resolution,[],[f82,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f64,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.57    inference(flattening,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.57    inference(nnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    r2_hidden(sK0,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f211,f189])).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    sK0 = sK1),
% 0.21/0.57    inference(subsumption_resolution,[],[f188,f104])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ~r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f103,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f55,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f45,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  % (28713)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | ~r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f101,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    r2_hidden(sK1,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f100,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    v3_ordinal1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f99,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    v3_ordinal1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.21/0.57    inference(resolution,[],[f46,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.21/0.57    inference(definition_unfolding,[],[f43,f67])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f184])).
% 0.21/0.57  fof(f184,plain,(
% 0.21/0.57    sK0 = sK1 | r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.21/0.57    inference(resolution,[],[f178,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f67])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | sK0 = sK1),
% 0.21/0.57    inference(resolution,[],[f121,f141])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.21/0.57    inference(resolution,[],[f139,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    r1_tarski(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f138,f104])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    r1_tarski(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f109,f41])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(X0,sK0) | r2_hidden(sK0,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f108,f40])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(X0,sK0) | ~v3_ordinal1(X0) | r2_hidden(sK0,X0) | ~v3_ordinal1(sK0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(X0,sK0) | ~v3_ordinal1(X0) | r2_hidden(sK0,X0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f105,f46])).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_ordinal1(X0,sK0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f49,f40])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    r1_tarski(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.21/0.57    inference(resolution,[],[f119,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.21/0.57    inference(definition_unfolding,[],[f42,f67])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f106,f40])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X1] : (~v3_ordinal1(X1) | r1_tarski(X1,sK1) | ~r1_ordinal1(X1,sK1)) )),
% 0.21/0.57    inference(resolution,[],[f49,f41])).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    r2_hidden(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f193,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 0.21/0.57    inference(equality_resolution,[],[f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | X0 != X1) )),
% 0.21/0.57    inference(definition_unfolding,[],[f56,f67])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | r2_hidden(sK1,sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f101,f189])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (28733)------------------------------
% 0.21/0.57  % (28733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28733)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (28733)Memory used [KB]: 6268
% 0.21/0.57  % (28733)Time elapsed: 0.127 s
% 0.21/0.57  % (28733)------------------------------
% 0.21/0.57  % (28733)------------------------------
% 0.21/0.57  % (28727)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (28715)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (28729)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (28710)Success in time 0.204 s
%------------------------------------------------------------------------------
