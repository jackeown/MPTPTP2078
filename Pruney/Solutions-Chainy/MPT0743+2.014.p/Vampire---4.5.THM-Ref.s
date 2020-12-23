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
% DateTime   : Thu Dec  3 12:55:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 (1153 expanded)
%              Number of leaves         :   11 ( 302 expanded)
%              Depth                    :   29
%              Number of atoms          :  242 (5274 expanded)
%              Number of equality atoms :   20 ( 222 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f584,plain,(
    $false ),
    inference(subsumption_resolution,[],[f583,f66])).

fof(f66,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f583,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(forward_demodulation,[],[f582,f396])).

fof(f396,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f392,f66])).

fof(f392,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK1,k1_ordinal1(sK1)) ),
    inference(resolution,[],[f349,f195])).

fof(f195,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | ~ r2_hidden(sK1,X2) ) ),
    inference(resolution,[],[f190,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f190,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f183,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f183,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f150,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f150,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f142,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f142,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f141,f70])).

fof(f70,plain,(
    v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f141,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f140,f41])).

fof(f41,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f42,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f349,plain,
    ( r1_tarski(k1_ordinal1(sK1),sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f348,f77])).

fof(f77,plain,(
    v3_ordinal1(k1_ordinal1(sK1)) ),
    inference(resolution,[],[f41,f46])).

fof(f348,plain,
    ( sK0 = sK1
    | r1_tarski(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1)) ),
    inference(subsumption_resolution,[],[f347,f40])).

fof(f347,plain,
    ( sK0 = sK1
    | r1_tarski(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1)) ),
    inference(resolution,[],[f330,f49])).

fof(f330,plain,
    ( r1_ordinal1(k1_ordinal1(sK1),sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f329,f77])).

fof(f329,plain,
    ( sK0 = sK1
    | r1_ordinal1(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1)) ),
    inference(subsumption_resolution,[],[f328,f40])).

fof(f328,plain,
    ( sK0 = sK1
    | r1_ordinal1(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1)) ),
    inference(resolution,[],[f173,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

% (23502)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f173,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK1))
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(resolution,[],[f166,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f166,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f157,f48])).

fof(f157,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f149,f56])).

fof(f149,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f148,f70])).

fof(f148,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f145,f41])).

fof(f145,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f43,f47])).

fof(f43,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f582,plain,(
    ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f438,f549])).

fof(f549,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f548,f396])).

fof(f548,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f399,f547])).

fof(f547,plain,(
    r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f546,f48])).

fof(f546,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(forward_demodulation,[],[f398,f396])).

fof(f398,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f42,f396])).

fof(f399,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f43,f396])).

fof(f438,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(backward_demodulation,[],[f150,f396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:43:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.49  % (23489)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (23493)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (23494)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (23494)Refutation not found, incomplete strategy% (23494)------------------------------
% 0.20/0.50  % (23494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23494)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23494)Memory used [KB]: 10746
% 0.20/0.50  % (23494)Time elapsed: 0.108 s
% 0.20/0.50  % (23494)------------------------------
% 0.20/0.50  % (23494)------------------------------
% 0.20/0.50  % (23490)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (23505)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (23487)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (23488)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (23485)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (23507)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (23486)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (23505)Refutation not found, incomplete strategy% (23505)------------------------------
% 0.20/0.52  % (23505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23505)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23499)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (23505)Memory used [KB]: 1663
% 0.20/0.52  % (23505)Time elapsed: 0.116 s
% 0.20/0.52  % (23505)------------------------------
% 0.20/0.52  % (23505)------------------------------
% 0.20/0.52  % (23497)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (23484)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (23501)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (23501)Refutation not found, incomplete strategy% (23501)------------------------------
% 0.20/0.52  % (23501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23501)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23501)Memory used [KB]: 10618
% 0.20/0.52  % (23501)Time elapsed: 0.127 s
% 0.20/0.52  % (23501)------------------------------
% 0.20/0.52  % (23501)------------------------------
% 0.20/0.52  % (23507)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f584,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f583,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.52  fof(f583,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f582,f396])).
% 0.20/0.52  fof(f396,plain,(
% 0.20/0.52    sK0 = sK1),
% 0.20/0.52    inference(subsumption_resolution,[],[f392,f66])).
% 0.20/0.52  fof(f392,plain,(
% 0.20/0.52    sK0 = sK1 | ~r2_hidden(sK1,k1_ordinal1(sK1))),
% 0.20/0.52    inference(resolution,[],[f349,f195])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ( ! [X2] : (~r1_tarski(X2,sK0) | ~r2_hidden(sK1,X2)) )),
% 0.20/0.52    inference(resolution,[],[f190,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ~r2_hidden(sK1,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f183,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f150,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ~r2_hidden(sK1,k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f142,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f141,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.52    inference(resolution,[],[f40,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : ((v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    v3_ordinal1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f140,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    v3_ordinal1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.52    inference(resolution,[],[f42,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f349,plain,(
% 0.20/0.52    r1_tarski(k1_ordinal1(sK1),sK0) | sK0 = sK1),
% 0.20/0.52    inference(subsumption_resolution,[],[f348,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    v3_ordinal1(k1_ordinal1(sK1))),
% 0.20/0.52    inference(resolution,[],[f41,f46])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    sK0 = sK1 | r1_tarski(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(k1_ordinal1(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f347,f40])).
% 0.20/0.52  fof(f347,plain,(
% 0.20/0.52    sK0 = sK1 | r1_tarski(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK1))),
% 0.20/0.52    inference(resolution,[],[f330,f49])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    r1_ordinal1(k1_ordinal1(sK1),sK0) | sK0 = sK1),
% 0.20/0.52    inference(subsumption_resolution,[],[f329,f77])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    sK0 = sK1 | r1_ordinal1(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(k1_ordinal1(sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f328,f40])).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    sK0 = sK1 | r1_ordinal1(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK1))),
% 0.20/0.52    inference(resolution,[],[f173,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.52  % (23502)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_ordinal1(sK1)) | sK0 = sK1),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f169])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    sK0 = sK1 | sK0 = sK1 | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.52    inference(resolution,[],[f166,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.20/0.52    inference(subsumption_resolution,[],[f157,f48])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f149,f56])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_ordinal1(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f148,f70])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK1) | r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f145,f41])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK1) | r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.52    inference(resolution,[],[f43,f47])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f582,plain,(
% 0.20/0.52    ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f438,f549])).
% 0.20/0.52  fof(f549,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK0)),
% 0.20/0.52    inference(forward_demodulation,[],[f548,f396])).
% 0.20/0.52  fof(f548,plain,(
% 0.20/0.52    ~r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f399,f547])).
% 0.20/0.52  fof(f547,plain,(
% 0.20/0.52    r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f546,f48])).
% 0.20/0.52  fof(f546,plain,(
% 0.20/0.52    r2_hidden(sK0,sK0) | r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.20/0.52    inference(forward_demodulation,[],[f398,f396])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f42,f396])).
% 0.20/0.52  fof(f399,plain,(
% 0.20/0.52    ~r1_ordinal1(k1_ordinal1(sK0),sK0) | ~r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f43,f396])).
% 0.20/0.52  fof(f438,plain,(
% 0.20/0.52    r2_hidden(sK0,sK0) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.20/0.52    inference(backward_demodulation,[],[f150,f396])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (23507)------------------------------
% 0.20/0.52  % (23507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23507)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (23507)Memory used [KB]: 1918
% 0.20/0.52  % (23507)Time elapsed: 0.085 s
% 0.20/0.52  % (23507)------------------------------
% 0.20/0.52  % (23507)------------------------------
% 0.20/0.52  % (23496)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (23512)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (23511)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (23504)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (23504)Refutation not found, incomplete strategy% (23504)------------------------------
% 0.20/0.53  % (23504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23504)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23504)Memory used [KB]: 10746
% 0.20/0.53  % (23504)Time elapsed: 0.130 s
% 0.20/0.53  % (23504)------------------------------
% 0.20/0.53  % (23504)------------------------------
% 0.20/0.53  % (23509)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (23513)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (23508)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (23500)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (23503)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (23510)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (23491)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (23492)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (23506)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (23495)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (23495)Refutation not found, incomplete strategy% (23495)------------------------------
% 0.20/0.54  % (23495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23495)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23495)Memory used [KB]: 10746
% 0.20/0.54  % (23495)Time elapsed: 0.151 s
% 0.20/0.54  % (23495)------------------------------
% 0.20/0.54  % (23495)------------------------------
% 0.20/0.54  % (23498)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (23483)Success in time 0.196 s
%------------------------------------------------------------------------------
