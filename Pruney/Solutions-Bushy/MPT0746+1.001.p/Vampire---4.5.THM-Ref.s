%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0746+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:35 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 310 expanded)
%              Number of leaves         :    7 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  108 ( 866 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f757,plain,(
    $false ),
    inference(global_subsumption,[],[f287,f746])).

fof(f746,plain,(
    ~ r2_hidden(sK2(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),k3_tarski(sK0)),sK2(sK0,k1_ordinal1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f57,f284,f30])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f284,plain,(
    ~ sP4(sK2(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),k3_tarski(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f283,f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ sP4(sK2(X1,k3_tarski(X2)),X2)
      | r1_tarski(X1,k3_tarski(X2)) ) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f283,plain,(
    ~ r1_tarski(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f83,f278,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f278,plain,(
    ~ r1_ordinal1(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f83,f66,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f66,plain,(
    ~ r2_hidden(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),k1_ordinal1(k3_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f29])).

fof(f47,plain,(
    ~ r1_tarski(sK0,k1_ordinal1(k3_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f42,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_tarski(X0,X1)
          | ~ v3_ordinal1(X1) )
      & ! [X2] :
          ( v3_ordinal1(X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ( v3_ordinal1(X1)
             => ~ r1_tarski(X0,X1) )
          & ! [X2] :
              ( r2_hidden(X2,X0)
             => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ( v3_ordinal1(X1)
             => ~ r1_tarski(X0,X1) )
          & ! [X1] :
              ( r2_hidden(X1,X0)
             => v3_ordinal1(X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

fof(f42,plain,(
    v3_ordinal1(k1_ordinal1(k3_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f83,plain,(
    v3_ordinal1(sK2(sK0,k1_ordinal1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f47,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(sK0,X0))
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f28,f18])).

fof(f18,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    v3_ordinal1(k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | v3_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(f39,plain,
    ( v3_ordinal1(sK1(sK0))
    | v3_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    r2_hidden(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f28])).

fof(f287,plain,(
    r2_hidden(sK2(sK2(sK0,k1_ordinal1(k3_tarski(sK0))),k3_tarski(sK0)),sK2(sK0,k1_ordinal1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f283,f28])).

%------------------------------------------------------------------------------
