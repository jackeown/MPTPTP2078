%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0747+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  90 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 280 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(subsumption_resolution,[],[f262,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f262,plain,(
    r2_hidden(sK0,sK0) ),
    inference(resolution,[],[f257,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f257,plain,(
    v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f256,f204])).

fof(f204,plain,(
    v1_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f203,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f203,plain,
    ( r1_tarski(sK1(sK0),sK0)
    | v1_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( r1_tarski(sK1(sK0),sK0)
    | v1_ordinal1(sK0)
    | r1_tarski(sK1(sK0),sK0) ),
    inference(resolution,[],[f124,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f124,plain,(
    ! [X4] :
      ( r2_hidden(sK4(sK1(sK0),X4),sK0)
      | r1_tarski(sK1(sK0),X4)
      | v1_ordinal1(sK0) ) ),
    inference(resolution,[],[f58,f24])).

fof(f58,plain,(
    ! [X0] :
      ( v3_ordinal1(sK4(sK1(sK0),X0))
      | v1_ordinal1(sK0)
      | r1_tarski(sK1(sK0),X0) ) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1(sK0))
      | v3_ordinal1(X0)
      | v1_ordinal1(sK0) ) ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,
    ( v3_ordinal1(sK1(sK0))
    | v1_ordinal1(sK0) ),
    inference(resolution,[],[f28,f25])).

fof(f25,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f256,plain,
    ( ~ v1_ordinal1(sK0)
    | v3_ordinal1(sK0) ),
    inference(resolution,[],[f255,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(f255,plain,(
    v2_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f254,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
     => v2_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f254,plain,
    ( r2_hidden(sK2(sK0),sK3(sK0))
    | v2_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f253,f33])).

fof(f33,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f253,plain,
    ( sK2(sK0) = sK3(sK0)
    | r2_hidden(sK2(sK0),sK3(sK0))
    | v2_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f247,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f247,plain,
    ( r2_hidden(sK3(sK0),sK2(sK0))
    | sK2(sK0) = sK3(sK0)
    | r2_hidden(sK2(sK0),sK3(sK0))
    | v2_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( r2_hidden(sK3(sK0),sK2(sK0))
    | sK2(sK0) = sK3(sK0)
    | r2_hidden(sK2(sK0),sK3(sK0))
    | v2_ordinal1(sK0)
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,
    ( v3_ordinal1(sK3(sK0))
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(X4)
      | r2_hidden(X4,sK2(sK0))
      | sK2(sK0) = X4
      | r2_hidden(sK2(sK0),X4)
      | v2_ordinal1(sK0) ) ),
    inference(resolution,[],[f26,f41])).

fof(f41,plain,
    ( v3_ordinal1(sK2(sK0))
    | v2_ordinal1(sK0) ),
    inference(resolution,[],[f30,f25])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

%------------------------------------------------------------------------------
