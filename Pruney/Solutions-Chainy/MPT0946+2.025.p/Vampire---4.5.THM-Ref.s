%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 220 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   21
%              Number of atoms          :  311 (1058 expanded)
%              Number of equality atoms :   48 ( 213 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f35,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f127,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f126,f36])).

fof(f36,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f126,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f125,f118])).

fof(f118,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f117,f35])).

fof(f117,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f114,f36])).

fof(f114,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f102,f68])).

fof(f68,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f67,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f66,f39])).

fof(f66,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f101,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f71,f63])).

fof(f63,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f60,f39])).

fof(f60,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f70,f39])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(superposition,[],[f45,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f87,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f85,f63])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(superposition,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f125,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f124,f38])).

fof(f38,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f116,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f116,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f115,f36])).

fof(f115,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f113,f35])).

fof(f113,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f102,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (31241)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (31241)Refutation not found, incomplete strategy% (31241)------------------------------
% 0.22/0.48  % (31241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31241)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (31241)Memory used [KB]: 10490
% 0.22/0.48  % (31241)Time elapsed: 0.059 s
% 0.22/0.48  % (31241)------------------------------
% 0.22/0.48  % (31241)------------------------------
% 0.22/0.48  % (31242)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (31242)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f127,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v3_ordinal1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f28,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f126,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    v3_ordinal1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f118])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f35])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f36])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f102,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f67,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f66,f39])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.48    inference(resolution,[],[f41,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f71,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f39])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.48    inference(equality_resolution,[],[f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(rectify,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,k3_relat_1(k1_wellord2(X0))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f70,f39])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,k3_relat_1(k1_wellord2(X0))) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(superposition,[],[f45,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.48    inference(superposition,[],[f87,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f85,f63])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f84,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f39])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(superposition,[],[f40,f43])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    sK0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    sK0 = sK1 | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f116,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f115,f36])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f113,f35])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f102,f37])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (31242)------------------------------
% 0.22/0.48  % (31242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31242)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (31242)Memory used [KB]: 10618
% 0.22/0.48  % (31242)Time elapsed: 0.072 s
% 0.22/0.48  % (31242)------------------------------
% 0.22/0.48  % (31242)------------------------------
% 0.22/0.49  % (31239)Success in time 0.123 s
%------------------------------------------------------------------------------
