%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 743 expanded)
%              Number of leaves         :   12 ( 190 expanded)
%              Depth                    :   24
%              Number of atoms          :  319 (3422 expanded)
%              Number of equality atoms :   21 ( 114 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(subsumption_resolution,[],[f283,f232])).

fof(f232,plain,(
    ! [X2] : ~ r2_hidden(X2,X2) ),
    inference(subsumption_resolution,[],[f229,f59])).

fof(f59,plain,(
    ! [X0] : ~ r1_tarski(k1_ordinal1(X0),X0) ),
    inference(resolution,[],[f55,f58])).

fof(f58,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f229,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,X2)
      | r1_tarski(k1_ordinal1(X2),X2) ) ),
    inference(superposition,[],[f51,f226])).

fof(f226,plain,(
    ! [X0] : sK2(k1_ordinal1(X0),X0) = X0 ),
    inference(subsumption_resolution,[],[f225,f59])).

fof(f225,plain,(
    ! [X0] :
      ( sK2(k1_ordinal1(X0),X0) = X0
      | r1_tarski(k1_ordinal1(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0] :
      ( sK2(k1_ordinal1(X0),X0) = X0
      | r1_tarski(k1_ordinal1(X0),X0)
      | r1_tarski(k1_ordinal1(X0),X0) ) ),
    inference(resolution,[],[f127,f51])).

fof(f127,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(k1_ordinal1(X3),X4),X3)
      | sK2(k1_ordinal1(X3),X4) = X3
      | r1_tarski(k1_ordinal1(X3),X4) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

% (3105)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f283,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f282,f242])).

fof(f242,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f161,f241])).

fof(f241,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f239,f232])).

fof(f239,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK0) ),
    inference(resolution,[],[f216,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(sK0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f37,plain,(
    v3_ordinal1(sK1) ),
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

% (3104)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f98,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f96,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(sK0,X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f96,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f92,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f86,f78])).

fof(f78,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f74,f37])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(sK0,X0)
      | r1_ordinal1(X0,sK0) ) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f86,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(sK1,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f44,f37])).

fof(f216,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f211,f103])).

fof(f103,plain,
    ( r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f91,f37])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK0,X0)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK0,X0)
      | r2_hidden(X0,sK0)
      | ~ v3_ordinal1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK0,X0)
      | r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK0) ) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f211,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f205,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_ordinal1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f53,f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f205,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f197,f38])).

fof(f38,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f197,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1) ),
    inference(resolution,[],[f193,f37])).

fof(f193,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(sK0),X0)
      | ~ r1_ordinal1(k1_ordinal1(sK0),X0) ) ),
    inference(resolution,[],[f87,f36])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3)
      | r1_tarski(k1_ordinal1(X2),X3)
      | ~ r1_ordinal1(k1_ordinal1(X2),X3) ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f161,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f160,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f160,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f158,f55])).

fof(f158,plain,
    ( r2_hidden(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f157,f52])).

fof(f157,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f156,f36])).

fof(f156,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f113,f41])).

fof(f113,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f112,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f109,f42])).

fof(f109,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f106,f39])).

fof(f39,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f97,f36])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK1,X0)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK1,X0)
      | r2_hidden(X0,sK1)
      | ~ v3_ordinal1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK1,X0)
      | r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK1) ) ),
    inference(resolution,[],[f86,f42])).

fof(f282,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f244,f199])).

fof(f199,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f196,f59])).

fof(f196,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(resolution,[],[f193,f36])).

fof(f244,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f38,f242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 19:42:29 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.47  % (3111)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.47  % (3103)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.48  % (3101)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (3119)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.48  % (3096)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.48  % (3100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (3103)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (3117)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (3099)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (3117)Refutation not found, incomplete strategy% (3117)------------------------------
% 0.21/0.49  % (3117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3117)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3117)Memory used [KB]: 1663
% 0.21/0.49  % (3117)Time elapsed: 0.101 s
% 0.21/0.49  % (3117)------------------------------
% 0.21/0.49  % (3117)------------------------------
% 0.21/0.49  % (3102)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f232])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f229,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_ordinal1(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f55,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,X2) | r1_tarski(k1_ordinal1(X2),X2)) )),
% 0.21/0.50    inference(superposition,[],[f51,f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ( ! [X0] : (sK2(k1_ordinal1(X0),X0) = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f225,f59])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    ( ! [X0] : (sK2(k1_ordinal1(X0),X0) = X0 | r1_tarski(k1_ordinal1(X0),X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f217])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ( ! [X0] : (sK2(k1_ordinal1(X0),X0) = X0 | r1_tarski(k1_ordinal1(X0),X0) | r1_tarski(k1_ordinal1(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f127,f51])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X4,X3] : (r2_hidden(sK2(k1_ordinal1(X3),X4),X3) | sK2(k1_ordinal1(X3),X4) = X3 | r1_tarski(k1_ordinal1(X3),X4)) )),
% 0.21/0.50    inference(resolution,[],[f52,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  % (3105)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    r2_hidden(sK0,sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f282,f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    sK0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f241])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f239,f232])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK0)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f237])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | r2_hidden(sK0,sK0)),
% 0.21/0.50    inference(resolution,[],[f216,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK0,sK1) | r2_hidden(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f99,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f98,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    v3_ordinal1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  % (3104)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f96,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_ordinal1(sK0,X0) | ~v3_ordinal1(X0) | r1_tarski(sK0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f44,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v3_ordinal1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f36])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f86,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f74,f37])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK0,X0) | r1_ordinal1(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f43,f36])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_ordinal1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_ordinal1(sK1,X1) | ~v3_ordinal1(X1) | r1_tarski(sK1,X1)) )),
% 0.21/0.50    inference(resolution,[],[f44,f37])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    r2_hidden(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f211,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f91,f37])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK0,X0) | r2_hidden(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f36])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK0,X0) | r2_hidden(X0,sK0) | ~v3_ordinal1(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK0,X0) | r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f85,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f205,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_ordinal1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f53,f55])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f197,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | r1_tarski(k1_ordinal1(sK0),sK1)),
% 0.21/0.50    inference(resolution,[],[f193,f37])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(k1_ordinal1(sK0),X0) | ~r1_ordinal1(k1_ordinal1(sK0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f87,f36])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v3_ordinal1(X2) | ~v3_ordinal1(X3) | r1_tarski(k1_ordinal1(X2),X3) | ~r1_ordinal1(k1_ordinal1(X2),X3)) )),
% 0.21/0.50    inference(resolution,[],[f44,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f158,f55])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    r2_hidden(sK1,sK0) | r1_tarski(sK1,sK0) | sK0 = sK1),
% 0.21/0.50    inference(resolution,[],[f157,f52])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_ordinal1(sK0)) | r1_tarski(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f36])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_ordinal1(sK0)) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.50    inference(resolution,[],[f113,f41])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0)) | r1_tarski(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f37])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0))),
% 0.21/0.50    inference(resolution,[],[f109,f42])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f106,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~r2_hidden(sK0,sK1) | ~r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f97,f36])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK1,X0) | r2_hidden(X0,sK1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f37])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK1,X0) | r2_hidden(X0,sK1) | ~v3_ordinal1(sK1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(sK1,X0) | r2_hidden(X0,sK1) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK1)) )),
% 0.21/0.50    inference(resolution,[],[f86,f42])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f244,f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f196,f59])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    r1_tarski(k1_ordinal1(sK0),sK0) | ~r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.21/0.50    inference(resolution,[],[f193,f36])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f38,f242])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3103)------------------------------
% 0.21/0.50  % (3103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3103)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3103)Memory used [KB]: 6396
% 0.21/0.50  % (3103)Time elapsed: 0.088 s
% 0.21/0.50  % (3103)------------------------------
% 0.21/0.50  % (3103)------------------------------
% 0.21/0.50  % (3098)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (3095)Success in time 0.14 s
%------------------------------------------------------------------------------
