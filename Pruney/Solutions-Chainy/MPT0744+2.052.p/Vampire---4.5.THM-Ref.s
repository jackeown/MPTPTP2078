%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 591 expanded)
%              Number of leaves         :   10 ( 160 expanded)
%              Depth                    :   24
%              Number of atoms          :  247 (2830 expanded)
%              Number of equality atoms :   25 ( 101 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163,f54])).

fof(f54,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f49])).

% (5622)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (5625)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f163,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f162,f139])).

fof(f139,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f138,f105])).

fof(f105,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f103,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (5628)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f103,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f101,f29])).

fof(f29,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f101,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f68,f93])).

fof(f93,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f92,f30])).

fof(f30,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f91,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f88,f30])).

fof(f88,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f62,f73])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f46,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK0,X3)
      | r1_ordinal1(X3,sK0)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f68,plain,(
    ! [X1] :
      ( r1_ordinal1(X1,sK1)
      | ~ r1_tarski(X1,sK1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f137,f29])).

fof(f137,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f128,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f30,f37])).

fof(f128,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f123,f77])).

fof(f77,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f121,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f121,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f120,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f86,f93])).

fof(f86,plain,(
    ! [X0] :
      ( r1_ordinal1(sK0,X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( r1_ordinal1(sK0,X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f61,f59])).

fof(f61,plain,(
    ! [X2] :
      ( r1_ordinal1(sK0,X2)
      | r1_ordinal1(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f29,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f162,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f141,f58])).

fof(f58,plain,(
    r1_ordinal1(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f29,f52,f29,f38])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f141,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(backward_demodulation,[],[f46,f139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:03:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (5623)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (5633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (5633)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (5623)Refutation not found, incomplete strategy% (5623)------------------------------
% 0.20/0.55  % (5623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5623)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5623)Memory used [KB]: 1663
% 0.20/0.55  % (5623)Time elapsed: 0.136 s
% 0.20/0.55  % (5623)------------------------------
% 0.20/0.55  % (5623)------------------------------
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f163,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 0.20/0.56    inference(equality_resolution,[],[f49])).
% 0.20/0.56  % (5622)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.56  % (5625)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 0.20/0.56    inference(definition_unfolding,[],[f44,f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.56    inference(flattening,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.20/0.56    inference(forward_demodulation,[],[f162,f139])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    sK0 = sK1),
% 0.20/0.56    inference(subsumption_resolution,[],[f138,f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 0.20/0.56    inference(resolution,[],[f103,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  % (5628)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(flattening,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    r1_tarski(sK1,sK0) | ~r1_tarski(sK0,sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f101,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    v3_ordinal1(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.56    inference(flattening,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.56    inference(negated_conjecture,[],[f9])).
% 0.20/0.56  fof(f9,conjecture,(
% 0.20/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0)),
% 0.20/0.56    inference(resolution,[],[f68,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.20/0.56    inference(subsumption_resolution,[],[f92,f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    v3_ordinal1(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.56    inference(resolution,[],[f91,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_ordinal1(X0,sK0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(resolution,[],[f29,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.56    inference(flattening,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    r1_ordinal1(sK1,sK0) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f88,f30])).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.56    inference(resolution,[],[f62,f73])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ~r2_hidden(sK0,sK1) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.56    inference(resolution,[],[f46,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f43,f34])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.56    inference(definition_unfolding,[],[f32,f34])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X3] : (r2_hidden(sK0,X3) | r1_ordinal1(X3,sK0) | ~v3_ordinal1(X3)) )),
% 0.20/0.56    inference(resolution,[],[f29,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.56    inference(flattening,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ( ! [X1] : (r1_ordinal1(X1,sK1) | ~r1_tarski(X1,sK1) | ~v3_ordinal1(X1)) )),
% 0.20/0.56    inference(resolution,[],[f30,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    sK0 = sK1 | r1_tarski(sK0,sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f137,f29])).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    sK0 = sK1 | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.56    inference(resolution,[],[f128,f67])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(resolution,[],[f30,f37])).
% 0.20/0.56  fof(f128,plain,(
% 0.20/0.56    r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 0.20/0.56    inference(resolution,[],[f123,f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    r2_hidden(sK0,sK1) | r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 0.20/0.56    inference(resolution,[],[f47,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.20/0.56    inference(definition_unfolding,[],[f42,f34])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | r1_ordinal1(sK0,sK1)),
% 0.20/0.56    inference(definition_unfolding,[],[f31,f34])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ~r2_hidden(sK0,sK1)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f121,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.56  fof(f121,plain,(
% 0.20/0.56    r1_tarski(sK1,sK0)),
% 0.20/0.56    inference(subsumption_resolution,[],[f120,f30])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    ~v3_ordinal1(sK1) | r1_tarski(sK1,sK0)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f116])).
% 0.20/0.56  fof(f116,plain,(
% 0.20/0.56    ~v3_ordinal1(sK1) | r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.20/0.56    inference(resolution,[],[f86,f93])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0] : (r1_ordinal1(sK0,X0) | ~v3_ordinal1(X0) | r1_tarski(X0,sK0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ( ! [X0] : (r1_ordinal1(sK0,X0) | ~v3_ordinal1(X0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(resolution,[],[f61,f59])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X2] : (r1_ordinal1(sK0,X2) | r1_ordinal1(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.20/0.56    inference(resolution,[],[f29,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.56    inference(flattening,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.56    inference(subsumption_resolution,[],[f141,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    r1_ordinal1(sK0,sK0)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f29,f52,f29,f38])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f141,plain,(
% 0.20/0.56    ~r1_ordinal1(sK0,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.20/0.56    inference(backward_demodulation,[],[f46,f139])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (5633)------------------------------
% 0.20/0.56  % (5633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5633)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (5633)Memory used [KB]: 6268
% 0.20/0.56  % (5633)Time elapsed: 0.139 s
% 0.20/0.56  % (5633)------------------------------
% 0.20/0.56  % (5633)------------------------------
% 0.20/0.56  % (5621)Success in time 0.2 s
%------------------------------------------------------------------------------
