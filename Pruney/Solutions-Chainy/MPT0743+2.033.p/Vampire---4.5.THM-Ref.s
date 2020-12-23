%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 (2698 expanded)
%              Number of leaves         :   10 ( 727 expanded)
%              Depth                    :   24
%              Number of atoms          :  263 (13175 expanded)
%              Number of equality atoms :   19 ( 180 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f304,f289])).

fof(f289,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f288,f233])).

fof(f233,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f228,f221])).

fof(f221,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f220,f146])).

fof(f146,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f118,f127])).

fof(f127,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f48,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f126,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f88,f107])).

fof(f107,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f82,f48])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f47,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X7] :
      ( r1_ordinal1(X7,sK0)
      | ~ v3_ordinal1(X7)
      | r2_hidden(sK0,X7) ) ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f118,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f117,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f117,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f116,f48])).

fof(f116,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f87,f104])).

fof(f104,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f81,f48])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(sK0,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f47,f51])).

fof(f87,plain,(
    ! [X6] :
      ( r1_ordinal1(sK0,X6)
      | ~ v3_ordinal1(X6)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f47,f54])).

fof(f220,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f219,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f38])).

% (2471)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f219,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f216,f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f115,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f115,plain,
    ( r1_tarski(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f112,f66])).

fof(f112,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f111,f107])).

fof(f111,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f48])).

fof(f110,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_ordinal1(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f85,f104])).

fof(f85,plain,(
    ! [X4] :
      ( r1_ordinal1(sK0,X4)
      | ~ v3_ordinal1(X4)
      | r1_ordinal1(X4,sK0) ) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f216,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f205,f49])).

fof(f49,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f205,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f169,f47])).

fof(f169,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r1_ordinal1(k1_ordinal1(X2),sK1)
      | ~ r2_hidden(sK1,k1_ordinal1(X2)) ) ),
    inference(resolution,[],[f134,f66])).

fof(f134,plain,(
    ! [X0] :
      ( r1_tarski(k1_ordinal1(X0),sK1)
      | ~ r1_ordinal1(k1_ordinal1(X0),sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f92,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X1,sK1)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f48,f51])).

fof(f228,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f223,f173])).

fof(f173,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f172,f47])).

fof(f172,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f144,f58])).

fof(f144,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X7] :
      ( r1_ordinal1(X7,sK1)
      | ~ v3_ordinal1(X7)
      | r2_hidden(sK1,X7) ) ),
    inference(resolution,[],[f48,f54])).

fof(f223,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | sK0 = sK1 ),
    inference(resolution,[],[f220,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f288,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f235,f187])).

fof(f187,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f185,f75])).

fof(f75,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f185,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f159,f47])).

fof(f159,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r1_ordinal1(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(sK0,k1_ordinal1(X2)) ) ),
    inference(resolution,[],[f105,f66])).

fof(f105,plain,(
    ! [X0] :
      ( r1_tarski(k1_ordinal1(X0),sK0)
      | ~ r1_ordinal1(k1_ordinal1(X0),sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f82,f58])).

fof(f235,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f49,f233])).

fof(f304,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f303,f233])).

fof(f303,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f252,f289])).

fof(f252,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f123,f233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:55:14 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.50  % (2448)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (2447)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (2467)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (2458)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (2455)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (2456)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (2442)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (2443)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (2464)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (2473)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (2469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (2461)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (2444)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (2452)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (2450)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (2466)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (2445)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (2472)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (2449)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2461)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (2470)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (2468)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (2451)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (2453)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (2468)Refutation not found, incomplete strategy% (2468)------------------------------
% 0.21/0.53  % (2468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2468)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2468)Memory used [KB]: 10746
% 0.21/0.53  % (2468)Time elapsed: 0.130 s
% 0.21/0.53  % (2468)------------------------------
% 0.21/0.53  % (2468)------------------------------
% 0.21/0.53  % (2457)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (2460)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (2462)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f304,f289])).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    r2_hidden(sK0,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f288,f233])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    sK0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f228,f221])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f220,f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f118,f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    r1_tarski(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f126,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v3_ordinal1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f19])).
% 0.21/0.54  fof(f19,conjecture,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f88,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ~r1_ordinal1(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f82,f48])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f47,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v3_ordinal1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X7] : (r1_ordinal1(X7,sK0) | ~v3_ordinal1(X7) | r2_hidden(sK0,X7)) )),
% 0.21/0.54    inference(resolution,[],[f47,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK0) | r2_hidden(sK1,sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f117,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f116,f48])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f87,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f81,f48])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(sK0,X0) | r1_tarski(sK0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f47,f51])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X6] : (r1_ordinal1(sK0,X6) | ~v3_ordinal1(X6) | r2_hidden(X6,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f47,f54])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f219,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  % (2471)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f216,f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f115,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f112,f66])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f111,f107])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    r1_ordinal1(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f48])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r1_ordinal1(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f85,f104])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X4] : (r1_ordinal1(sK0,X4) | ~v3_ordinal1(X4) | r1_ordinal1(X4,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f47,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.21/0.54    inference(resolution,[],[f205,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.21/0.54    inference(resolution,[],[f169,f47])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X2] : (~v3_ordinal1(X2) | ~r1_ordinal1(k1_ordinal1(X2),sK1) | ~r2_hidden(sK1,k1_ordinal1(X2))) )),
% 0.21/0.54    inference(resolution,[],[f134,f66])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_ordinal1(X0),sK1) | ~r1_ordinal1(k1_ordinal1(X0),sK1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f92,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK1) | r1_tarski(X1,sK1)) )),
% 0.21/0.54    inference(resolution,[],[f48,f51])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    sK0 = sK1 | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f223,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f47])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f144,f58])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f98,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X7] : (r1_ordinal1(X7,sK1) | ~v3_ordinal1(X7) | r2_hidden(sK1,X7)) )),
% 0.21/0.54    inference(resolution,[],[f48,f54])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_ordinal1(sK0)) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f220,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f235,f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f185,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK0) | ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.21/0.54    inference(resolution,[],[f159,f47])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X2] : (~v3_ordinal1(X2) | ~r1_ordinal1(k1_ordinal1(X2),sK0) | ~r2_hidden(sK0,k1_ordinal1(X2))) )),
% 0.21/0.54    inference(resolution,[],[f105,f66])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_ordinal1(X0),sK0) | ~r1_ordinal1(k1_ordinal1(X0),sK0) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f82,f58])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f49,f233])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f303,f233])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f252,f289])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK0) | ~r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f123,f233])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (2461)------------------------------
% 0.21/0.54  % (2461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2461)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (2461)Memory used [KB]: 1791
% 0.21/0.54  % (2461)Time elapsed: 0.125 s
% 0.21/0.54  % (2461)------------------------------
% 0.21/0.54  % (2461)------------------------------
% 0.21/0.55  % (2439)Success in time 0.186 s
%------------------------------------------------------------------------------
