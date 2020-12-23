%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0738+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 148 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 481 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85,f75])).

fof(f75,plain,(
    ~ r1_ordinal1(sK0,sK0) ),
    inference(backward_demodulation,[],[f19,f73])).

fof(f73,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f72,f39])).

fof(f39,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f18,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f18,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f72,plain,
    ( sK0 = sK1
    | ~ v1_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f71,f57])).

fof(f57,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f56,f18])).

fof(f56,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f53,f21])).

fof(f21,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f71,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1)
    | ~ v1_ordinal1(sK1) ),
    inference(resolution,[],[f61,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f61,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f60,f18])).

fof(f60,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f58,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f20,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    r1_ordinal1(sK0,sK0) ),
    inference(backward_demodulation,[],[f55,f73])).

fof(f55,plain,(
    r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f54,f21])).

fof(f54,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f51,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r1_ordinal1(sK1,sK0) ),
    inference(resolution,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

%------------------------------------------------------------------------------
