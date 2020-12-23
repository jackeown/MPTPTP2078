%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0950+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:57 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 841 expanded)
%              Number of leaves         :   20 ( 203 expanded)
%              Depth                    :   28
%              Number of atoms          :  485 (2879 expanded)
%              Number of equality atoms :   45 ( 159 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1426,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1425,f68])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1425,plain,(
    ~ v1_relat_1(k1_wellord2(sK5(sK0,k1_wellord2(sK1)))) ),
    inference(subsumption_resolution,[],[f1424,f68])).

fof(f1424,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK5(sK0,k1_wellord2(sK1)))) ),
    inference(subsumption_resolution,[],[f1421,f1103])).

fof(f1103,plain,(
    ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK5(sK0,k1_wellord2(sK1)))) ),
    inference(resolution,[],[f1094,f254])).

fof(f254,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f253,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f113,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f113,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | v3_ordinal1(X3) ) ),
    inference(resolution,[],[f65,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_ordinal1)).

fof(f65,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1)
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f49])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1)
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r1_tarski(X0,X1)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r1_tarski(X0,X1)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord2)).

fof(f253,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f252,f68])).

fof(f252,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v1_relat_1(k1_wellord2(sK0)) ) ),
    inference(subsumption_resolution,[],[f251,f129])).

fof(f129,plain,(
    v2_wellord1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f126,f65])).

fof(f126,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f66,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k1_wellord2(X1))
      | ~ r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_wellord1(k1_wellord2(X1))
          | ~ r1_tarski(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_wellord2)).

fof(f66,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v2_wellord1(k1_wellord2(sK0))
      | ~ v1_relat_1(k1_wellord2(sK0)) ) ),
    inference(superposition,[],[f240,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_wellord2(X0) = X1
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_wellord2(X0) = X1
              | ~ r4_wellord1(X0,k1_wellord2(X1)) )
            & ( r4_wellord1(X0,k1_wellord2(X1))
              | k2_wellord2(X0) != X1 ) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( k2_wellord2(X0) = X1
            <=> r4_wellord1(X0,k1_wellord2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord2)).

fof(f240,plain,(
    ~ r2_hidden(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f237,f109])).

fof(f109,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f65,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f237,plain,
    ( ~ r2_hidden(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ v1_ordinal1(sK1) ),
    inference(resolution,[],[f197,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK2(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f197,plain,(
    ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f193,f68])).

fof(f193,plain,
    ( ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f134,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_wellord2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_wellord2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v3_ordinal1(k2_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord2)).

fof(f134,plain,
    ( ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f130,f65])).

fof(f130,plain,
    ( ~ r1_tarski(k2_wellord2(k1_wellord2(sK0)),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0))) ),
    inference(resolution,[],[f67,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f67,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1094,plain,(
    r2_hidden(sK5(sK0,k1_wellord2(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f1093,f68])).

fof(f1093,plain,
    ( r2_hidden(sK5(sK0,k1_wellord2(sK1)),sK1)
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(subsumption_resolution,[],[f1091,f66])).

fof(f1091,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r2_hidden(sK5(sK0,k1_wellord2(sK1)),sK1)
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f372,f107])).

fof(f107,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f372,plain,
    ( ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | r2_hidden(sK5(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1))) ),
    inference(subsumption_resolution,[],[f370,f246])).

fof(f246,plain,(
    ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f245,f68])).

fof(f245,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(subsumption_resolution,[],[f244,f68])).

fof(f244,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(resolution,[],[f218,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f218,plain,(
    ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(subsumption_resolution,[],[f217,f168])).

fof(f168,plain,(
    r1_ordinal1(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( r1_ordinal1(sK1,sK1)
    | r1_ordinal1(sK1,sK1) ),
    inference(resolution,[],[f115,f65])).

fof(f115,plain,(
    ! [X5] :
      ( ~ v3_ordinal1(X5)
      | r1_ordinal1(X5,sK1)
      | r1_ordinal1(sK1,X5) ) ),
    inference(resolution,[],[f65,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f217,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r1_ordinal1(sK1,sK1) ),
    inference(resolution,[],[f137,f65])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
      | ~ r1_ordinal1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f136,f68])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v1_relat_1(k1_wellord2(sK0)) ) ),
    inference(subsumption_resolution,[],[f133,f129])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v2_wellord1(k1_wellord2(sK0))
      | ~ v1_relat_1(k1_wellord2(sK0)) ) ),
    inference(superposition,[],[f67,f71])).

fof(f370,plain,
    ( r2_hidden(sK5(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(resolution,[],[f163,f181])).

fof(f181,plain,(
    v2_wellord1(k1_wellord2(sK1)) ),
    inference(resolution,[],[f171,f114])).

fof(f114,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK1)
      | v2_wellord1(k1_wellord2(X4)) ) ),
    inference(resolution,[],[f65,f77])).

fof(f171,plain,(
    r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f170,f65])).

fof(f170,plain,
    ( r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f168,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f163,plain,
    ( ~ v2_wellord1(k1_wellord2(sK1))
    | r2_hidden(sK5(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(subsumption_resolution,[],[f160,f68])).

fof(f160,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | r2_hidden(sK5(sK0,k1_wellord2(sK1)),k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f88,f124])).

fof(f124,plain,(
    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f66,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k3_relat_1(X1))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK5(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK5(X0,X1),k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK5(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK5(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] :
              ~ ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
                & r2_hidden(X2,k3_relat_1(X1)) )
          & ~ r4_wellord1(X1,k2_wellord1(X1,X0))
          & v2_wellord1(X1)
          & r1_tarski(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_wellord1)).

fof(f1421,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK5(sK0,k1_wellord2(sK1))))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK5(sK0,k1_wellord2(sK1)))) ),
    inference(resolution,[],[f1307,f72])).

fof(f1307,plain,(
    r4_wellord1(k1_wellord2(sK5(sK0,k1_wellord2(sK1))),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f1306,f68])).

fof(f1306,plain,
    ( r4_wellord1(k1_wellord2(sK5(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(subsumption_resolution,[],[f1304,f66])).

fof(f1304,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r4_wellord1(k1_wellord2(sK5(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f1298,f107])).

fof(f1298,plain,
    ( ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | r4_wellord1(k1_wellord2(sK5(sK0,k1_wellord2(sK1))),k1_wellord2(sK0)) ),
    inference(backward_demodulation,[],[f1120,f1295])).

fof(f1295,plain,(
    k1_wellord2(sK5(sK0,k1_wellord2(sK1))) = k2_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1))) ),
    inference(resolution,[],[f1100,f91])).

fof(f1100,plain,(
    r1_tarski(sK5(sK0,k1_wellord2(sK1)),sK1) ),
    inference(resolution,[],[f1094,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f109,f78])).

fof(f1120,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1))),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(backward_demodulation,[],[f375,f1105])).

fof(f1105,plain,(
    sK5(sK0,k1_wellord2(sK1)) = k1_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1))) ),
    inference(resolution,[],[f1094,f352])).

fof(f352,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | k1_wellord1(k1_wellord2(sK1),X5) = X5 ) ),
    inference(subsumption_resolution,[],[f351,f92])).

fof(f351,plain,(
    ! [X5] :
      ( k1_wellord1(k1_wellord2(sK1),X5) = X5
      | ~ m1_subset_1(X5,sK1)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(resolution,[],[f220,f65])).

fof(f220,plain,(
    ! [X2,X1] :
      ( ~ v3_ordinal1(X2)
      | k1_wellord1(k1_wellord2(sK1),X1) = X1
      | ~ m1_subset_1(X1,X2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f111,f76])).

fof(f111,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK1)
      | k1_wellord1(k1_wellord2(sK1),X1) = X1 ) ),
    inference(resolution,[],[f65,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f375,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(subsumption_resolution,[],[f373,f246])).

fof(f373,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(resolution,[],[f164,f181])).

fof(f164,plain,
    ( ~ v2_wellord1(k1_wellord2(sK1))
    | r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    inference(subsumption_resolution,[],[f161,f68])).

fof(f161,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK5(sK0,k1_wellord2(sK1)))),k1_wellord2(sK0))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ r1_tarski(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(superposition,[],[f89,f124])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK5(X0,X1))),k2_wellord1(X1,X0))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

%------------------------------------------------------------------------------
