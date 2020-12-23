%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 142 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :   18
%              Number of atoms          :  376 (1065 expanded)
%              Number of equality atoms :   43 ( 127 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f28])).

fof(f28,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    & ! [X3] :
        ( ( sK1 != X3
          & r2_hidden(k4_tarski(X3,sK1),sK2) )
        | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        & ! [X3] :
            ( ( X1 != X3
              & r2_hidden(k4_tarski(X3,X1),X2) )
            | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
      & ! [X3] :
          ( ( sK1 != X3
            & r2_hidden(k4_tarski(X3,sK1),sK2) )
          | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(f159,plain,(
    ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(resolution,[],[f153,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,X0),sK2)
      | ~ r2_hidden(X0,k3_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK2))
      | r2_hidden(k4_tarski(X0,X0),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f61,f27])).

fof(f27,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | r2_hidden(k4_tarski(X0,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_wellord1(X2,X1),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_wellord1(X2,X1),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | X0 != X1
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 ) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 ) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

% (18500)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f153,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK0),sK2) ),
    inference(superposition,[],[f32,f145])).

fof(f145,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f144,f28])).

fof(f144,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f143,f50])).

fof(f50,plain,(
    ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X3] :
      ( sK1 != X3
      | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f139,f29])).

fof(f29,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f139,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sK0 = sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(resolution,[],[f119,f32])).

fof(f119,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),sK2)
      | ~ r2_hidden(X3,k3_relat_1(sK2))
      | X2 = X3
      | r2_hidden(X3,k1_wellord1(sK2,X2))
      | ~ r2_hidden(X2,k3_relat_1(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k3_relat_1(sK2))
      | ~ r2_hidden(X3,k3_relat_1(sK2))
      | X2 = X3
      | r2_hidden(X3,k1_wellord1(sK2,X2))
      | r2_hidden(k4_tarski(X2,X3),sK2)
      | ~ r2_hidden(X3,k3_relat_1(sK2))
      | ~ r2_hidden(X2,k3_relat_1(sK2))
      | X2 = X3 ) ),
    inference(resolution,[],[f92,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK2)
      | r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | r2_hidden(k4_tarski(X1,X0),sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(resolution,[],[f69,f27])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | r2_hidden(k4_tarski(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | r2_hidden(k4_tarski(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & sK3(X0) != sK4(X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0))
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & sK3(X0) != sK4(X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0))
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_wellord1(sK2,X1))
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | X0 = X1
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(resolution,[],[f75,f27])).

fof(f75,plain,(
    ! [X6,X7,X5] :
      ( ~ v2_wellord1(X7)
      | r2_hidden(X5,k1_wellord1(X7,X6))
      | ~ r2_hidden(X6,k3_relat_1(X7))
      | ~ r2_hidden(X5,k3_relat_1(X7))
      | X5 = X6
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(X5,X6),X7) ) ),
    inference(duplicate_literal_removal,[],[f74])).

% (18509)Refutation not found, incomplete strategy% (18509)------------------------------
% (18509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18509)Termination reason: Refutation not found, incomplete strategy

% (18509)Memory used [KB]: 10490
% (18509)Time elapsed: 0.113 s
% (18509)------------------------------
% (18509)------------------------------
fof(f74,plain,(
    ! [X6,X7,X5] :
      ( X5 = X6
      | r2_hidden(X5,k1_wellord1(X7,X6))
      | ~ r2_hidden(X6,k3_relat_1(X7))
      | ~ r2_hidden(X5,k3_relat_1(X7))
      | ~ v2_wellord1(X7)
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(X5,X6),X7)
      | ~ r2_hidden(X6,k3_relat_1(X7))
      | ~ r2_hidden(X5,k3_relat_1(X7))
      | ~ v2_wellord1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (18499)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (18499)Refutation not found, incomplete strategy% (18499)------------------------------
% 0.20/0.51  % (18499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18499)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (18499)Memory used [KB]: 10618
% 0.20/0.51  % (18499)Time elapsed: 0.092 s
% 0.20/0.51  % (18499)------------------------------
% 0.20/0.51  % (18499)------------------------------
% 0.20/0.51  % (18503)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (18520)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (18517)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (18512)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (18522)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (18511)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (18514)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (18504)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (18505)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (18521)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (18514)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (18519)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (18511)Refutation not found, incomplete strategy% (18511)------------------------------
% 0.20/0.53  % (18511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18505)Refutation not found, incomplete strategy% (18505)------------------------------
% 0.20/0.53  % (18505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18505)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18505)Memory used [KB]: 1663
% 0.20/0.53  % (18505)Time elapsed: 0.108 s
% 0.20/0.53  % (18505)------------------------------
% 0.20/0.53  % (18505)------------------------------
% 0.20/0.53  % (18509)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (18504)Refutation not found, incomplete strategy% (18504)------------------------------
% 0.20/0.53  % (18504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18511)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18511)Memory used [KB]: 6140
% 0.20/0.53  % (18511)Time elapsed: 0.103 s
% 0.20/0.53  % (18511)------------------------------
% 0.20/0.53  % (18511)------------------------------
% 0.20/0.53  % (18508)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f159,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK0,sK1),sK2) & ! [X3] : ((sK1 != X3 & r2_hidden(k4_tarski(X3,sK1),sK2)) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r2_hidden(k4_tarski(sK0,sK1),sK2) & ! [X3] : ((sK1 != X3 & r2_hidden(k4_tarski(X3,sK1),sK2)) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~r2_hidden(k4_tarski(X0,X1),X2) & (! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(negated_conjecture,[],[f5])).
% 0.20/0.53  fof(f5,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.53    inference(resolution,[],[f153,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(k4_tarski(X0,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f64,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X0),sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(resolution,[],[f61,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    v2_wellord1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_wellord1(X1) | ~r2_hidden(X0,k3_relat_1(X1)) | r2_hidden(k4_tarski(X0,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X0),X1) | ~r2_hidden(X0,k3_relat_1(X1)) | ~r2_hidden(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(resolution,[],[f46,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r1_tarski(k1_wellord1(X2,X1),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r1_tarski(k1_wellord1(X2,X1),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(equality_resolution,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | X0 != X1 | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | (~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1)) & (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | (~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1)) & ((r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  % (18500)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK0,sK0),sK2)),
% 0.20/0.53    inference(superposition,[],[f32,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    sK0 = sK1),
% 0.20/0.53    inference(subsumption_resolution,[],[f144,f28])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    sK0 = sK1 | ~r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f143,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 0.20/0.53    inference(equality_resolution,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X3] : (sK1 != X3 | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    sK0 = sK1 | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k3_relat_1(sK2)) | sK0 = sK1 | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.53    inference(resolution,[],[f119,f32])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),sK2) | ~r2_hidden(X3,k3_relat_1(sK2)) | X2 = X3 | r2_hidden(X3,k1_wellord1(sK2,X2)) | ~r2_hidden(X2,k3_relat_1(sK2))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f114])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k3_relat_1(sK2)) | ~r2_hidden(X3,k3_relat_1(sK2)) | X2 = X3 | r2_hidden(X3,k1_wellord1(sK2,X2)) | r2_hidden(k4_tarski(X2,X3),sK2) | ~r2_hidden(X3,k3_relat_1(sK2)) | ~r2_hidden(X2,k3_relat_1(sK2)) | X2 = X3) )),
% 0.20/0.53    inference(resolution,[],[f92,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f87,f26])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,X0),sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.20/0.53    inference(resolution,[],[f69,f27])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v2_wellord1(X2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | r2_hidden(k4_tarski(X1,X0),X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | r2_hidden(k4_tarski(X1,X0),X2) | ~v1_relat_1(X2) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(resolution,[],[f33,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X4,X0,X3] : (~v6_relat_2(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | r2_hidden(k4_tarski(X4,X3),X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(rectify,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f91,f26])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.20/0.53    inference(resolution,[],[f75,f27])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X6,X7,X5] : (~v2_wellord1(X7) | r2_hidden(X5,k1_wellord1(X7,X6)) | ~r2_hidden(X6,k3_relat_1(X7)) | ~r2_hidden(X5,k3_relat_1(X7)) | X5 = X6 | ~v1_relat_1(X7) | ~r2_hidden(k4_tarski(X5,X6),X7)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f74])).
% 0.20/0.53  % (18509)Refutation not found, incomplete strategy% (18509)------------------------------
% 0.20/0.53  % (18509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18509)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18509)Memory used [KB]: 10490
% 0.20/0.53  % (18509)Time elapsed: 0.113 s
% 0.20/0.53  % (18509)------------------------------
% 0.20/0.53  % (18509)------------------------------
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X6,X7,X5] : (X5 = X6 | r2_hidden(X5,k1_wellord1(X7,X6)) | ~r2_hidden(X6,k3_relat_1(X7)) | ~r2_hidden(X5,k3_relat_1(X7)) | ~v2_wellord1(X7) | ~v1_relat_1(X7) | ~r2_hidden(k4_tarski(X5,X6),X7) | ~r2_hidden(X6,k3_relat_1(X7)) | ~r2_hidden(X5,k3_relat_1(X7)) | ~v2_wellord1(X7) | ~v1_relat_1(X7)) )),
% 0.20/0.53    inference(resolution,[],[f47,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | X0 = X1 | r2_hidden(X0,k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (18514)------------------------------
% 0.20/0.53  % (18514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18514)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (18514)Memory used [KB]: 1663
% 0.20/0.53  % (18514)Time elapsed: 0.111 s
% 0.20/0.53  % (18514)------------------------------
% 0.20/0.53  % (18514)------------------------------
% 0.20/0.53  % (18496)Success in time 0.166 s
%------------------------------------------------------------------------------
