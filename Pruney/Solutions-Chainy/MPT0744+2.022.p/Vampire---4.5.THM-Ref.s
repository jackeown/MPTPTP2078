%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 449 expanded)
%              Number of leaves         :    9 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          :  200 (2098 expanded)
%              Number of equality atoms :   24 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f50,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f41,f31])).

fof(f31,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f121,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f120,f104])).

fof(f104,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f103,f100])).

fof(f100,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f26,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f99,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f98,f91])).

fof(f91,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f90,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f90,plain,
    ( r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f64,f67])).

fof(f67,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f29,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2] :
      ( r1_ordinal1(X2,sK1)
      | r2_hidden(sK1,X2)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f27,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f71,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f39,f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f95,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f27,f26,f93,f34])).

fof(f93,plain,(
    r1_ordinal1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f27,f26,f91,f32])).

fof(f120,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f54,plain,(
    r1_ordinal1(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f26,f48,f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(backward_demodulation,[],[f42,f104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:32:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (11880)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.51  % (11888)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.51  % (11880)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(subsumption_resolution,[],[f121,f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 0.23/0.51    inference(equality_resolution,[],[f45])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 0.23/0.51    inference(definition_unfolding,[],[f41,f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.23/0.51    inference(flattening,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.23/0.51    inference(nnf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.23/0.51  fof(f121,plain,(
% 0.23/0.51    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.23/0.51    inference(forward_demodulation,[],[f120,f104])).
% 0.23/0.51  fof(f104,plain,(
% 0.23/0.51    sK0 = sK1),
% 0.23/0.51    inference(subsumption_resolution,[],[f103,f100])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    sK0 = sK1 | r1_tarski(sK0,sK1)),
% 0.23/0.51    inference(subsumption_resolution,[],[f99,f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    v3_ordinal1(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.23/0.51    inference(flattening,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,negated_conjecture,(
% 0.23/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.23/0.51    inference(negated_conjecture,[],[f8])).
% 0.23/0.51  fof(f8,conjecture,(
% 0.23/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    sK0 = sK1 | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f98,f91])).
% 0.23/0.51  fof(f91,plain,(
% 0.23/0.51    ~r2_hidden(sK0,sK1)),
% 0.23/0.51    inference(subsumption_resolution,[],[f90,f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,plain,(
% 0.23/0.51    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    r2_hidden(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 0.23/0.51    inference(subsumption_resolution,[],[f87,f26])).
% 0.23/0.51  fof(f87,plain,(
% 0.23/0.51    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~r2_hidden(sK0,sK1)),
% 0.23/0.51    inference(resolution,[],[f64,f67])).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 0.23/0.51    inference(resolution,[],[f42,f46])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 0.23/0.51    inference(definition_unfolding,[],[f40,f31])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~r1_ordinal1(sK0,sK1)),
% 0.23/0.51    inference(definition_unfolding,[],[f29,f31])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    ( ! [X2] : (r1_ordinal1(X2,sK1) | r2_hidden(sK1,X2) | ~v3_ordinal1(X2)) )),
% 0.23/0.51    inference(resolution,[],[f27,f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.23/0.51    inference(flattening,[],[f11])).
% 0.23/0.51  fof(f11,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    v3_ordinal1(sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f98,plain,(
% 0.23/0.51    r2_hidden(sK0,sK1) | sK0 = sK1 | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.23/0.51    inference(resolution,[],[f71,f62])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.23/0.51    inference(resolution,[],[f27,f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.23/0.51    inference(flattening,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.23/0.51  fof(f71,plain,(
% 0.23/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.23/0.51    inference(resolution,[],[f43,f47])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.23/0.51    inference(definition_unfolding,[],[f39,f31])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | r1_ordinal1(sK0,sK1)),
% 0.23/0.51    inference(definition_unfolding,[],[f28,f31])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f103,plain,(
% 0.23/0.51    sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 0.23/0.51    inference(resolution,[],[f95,f38])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.51    inference(flattening,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.51    inference(nnf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.51  fof(f95,plain,(
% 0.23/0.51    r1_tarski(sK1,sK0)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f27,f26,f93,f34])).
% 0.23/0.51  fof(f93,plain,(
% 0.23/0.51    r1_ordinal1(sK1,sK0)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f27,f26,f91,f32])).
% 0.23/0.51  fof(f120,plain,(
% 0.23/0.51    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.23/0.51    inference(subsumption_resolution,[],[f106,f54])).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    r1_ordinal1(sK0,sK0)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f26,f48,f26,f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.51    inference(equality_resolution,[],[f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f106,plain,(
% 0.23/0.51    ~r1_ordinal1(sK0,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.23/0.51    inference(backward_demodulation,[],[f42,f104])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (11880)------------------------------
% 0.23/0.51  % (11880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (11880)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (11880)Memory used [KB]: 6268
% 0.23/0.51  % (11880)Time elapsed: 0.077 s
% 0.23/0.51  % (11880)------------------------------
% 0.23/0.51  % (11880)------------------------------
% 0.23/0.51  % (11868)Success in time 0.135 s
%------------------------------------------------------------------------------
