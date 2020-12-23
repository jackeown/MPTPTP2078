%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 455 expanded)
%              Number of leaves         :    9 ( 122 expanded)
%              Depth                    :   24
%              Number of atoms          :  220 (2307 expanded)
%              Number of equality atoms :   30 ( 104 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f26])).

fof(f26,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
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

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f119,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f109,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(factoring,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f109,plain,(
    ~ r1_ordinal1(sK0,sK0) ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f30,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f108,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK0))
    | ~ r1_ordinal1(sK0,sK0) ),
    inference(forward_demodulation,[],[f94,f91])).

fof(f91,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f90,f88])).

fof(f88,plain,
    ( sK0 = sK1
    | ~ r1_ordinal1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ r1_ordinal1(sK1,sK0) ),
    inference(resolution,[],[f83,f72])).

fof(f72,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f71,f27])).

fof(f27,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f70,f26])).

fof(f70,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f60,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f56,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK1))
    | r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f83,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f82,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f81,f27])).

fof(f81,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f74,f34])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f69,f39])).

fof(f69,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f68,f27])).

fof(f68,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f62,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK1))
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f90,plain,
    ( sK0 = sK1
    | r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f89,f27])).

fof(f89,plain,
    ( sK0 = sK1
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,
    ( sK0 = sK1
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f83,f33])).

fof(f94,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(backward_demodulation,[],[f29,f91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (12085)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (12088)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (12081)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (12079)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (12088)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f119,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v3_ordinal1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ~v3_ordinal1(sK0)),
% 0.20/0.53    inference(resolution,[],[f109,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(factoring,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f108,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k1_ordinal1(sK0)) | ~r1_ordinal1(sK0,sK0)),
% 0.20/0.53    inference(forward_demodulation,[],[f94,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    sK0 = sK1),
% 0.20/0.53    inference(subsumption_resolution,[],[f90,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    sK0 = sK1 | ~r1_ordinal1(sK1,sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    sK0 = sK1 | sK0 = sK1 | ~r1_ordinal1(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f83,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~r1_ordinal1(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f71,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    v3_ordinal1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f70,f26])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.53    inference(resolution,[],[f60,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK0) | r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 0.20/0.53    inference(resolution,[],[f56,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    r2_hidden(sK0,sK1) | sK0 = sK1 | r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f36,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    r2_hidden(sK0,k1_ordinal1(sK1)) | r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 0.20/0.53    inference(subsumption_resolution,[],[f82,f26])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f27])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | sK0 = sK1 | ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.20/0.53    inference(resolution,[],[f74,f34])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK1) | ~r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 0.20/0.53    inference(resolution,[],[f69,f39])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | sK0 = sK1 | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f68,f27])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    sK0 = sK1 | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f62,f26])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    sK0 = sK1 | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f32,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ~r2_hidden(sK0,sK1) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f37,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k1_ordinal1(sK1)) | ~r1_ordinal1(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    sK0 = sK1 | r1_ordinal1(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f89,f27])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    sK0 = sK1 | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f87,f26])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    sK0 = sK1 | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.20/0.53    inference(resolution,[],[f83,f33])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK0) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.53    inference(backward_demodulation,[],[f29,f91])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (12088)------------------------------
% 0.20/0.53  % (12088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12088)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (12088)Memory used [KB]: 1791
% 0.20/0.53  % (12088)Time elapsed: 0.120 s
% 0.20/0.53  % (12088)------------------------------
% 0.20/0.53  % (12088)------------------------------
% 0.20/0.53  % (12078)Success in time 0.175 s
%------------------------------------------------------------------------------
