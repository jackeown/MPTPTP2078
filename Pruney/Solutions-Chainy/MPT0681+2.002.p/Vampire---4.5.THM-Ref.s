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
% DateTime   : Thu Dec  3 12:53:29 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 366 expanded)
%              Number of leaves         :   18 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  290 (1473 expanded)
%              Number of equality atoms :   56 ( 138 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f346,f339])).

fof(f339,plain,(
    ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f329,f140])).

fof(f140,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f111,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK8(X0),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(X0)
          & r2_hidden(sK8(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK9(X4),sK10(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK8(X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK9(X4),sK10(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

% (26359)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f111,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f110,f108])).

fof(f108,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f58,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f58,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f110,plain,(
    ! [X2] : ~ r2_hidden(X2,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK11(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f26,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK11(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f329,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f135,f325])).

fof(f325,plain,(
    ! [X8] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X8) ),
    inference(backward_demodulation,[],[f188,f323])).

fof(f323,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f322,f290])).

fof(f290,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f287,f108])).

fof(f287,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f102,f58])).

fof(f102,plain,(
    ! [X12,X11] :
      ( ~ r1_xboole_0(X11,X12)
      | k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X11,X12)) ) ),
    inference(forward_demodulation,[],[f97,f96])).

fof(f96,plain,(
    ! [X10,X9] : k7_relat_1(k7_relat_1(sK2,X9),X10) = k7_relat_1(sK2,k3_xboole_0(X9,X10)) ),
    inference(resolution,[],[f56,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X11),X12)
      | ~ r1_xboole_0(X11,X12) ) ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

% (26369)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f322,plain,(
    ! [X0] : k7_relat_1(k1_xboole_0,X0) = k7_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f317,f224])).

fof(f224,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f142,f79])).

fof(f142,plain,(
    ! [X13] : r1_xboole_0(k1_xboole_0,X13) ),
    inference(resolution,[],[f111,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK12(X0,X1),X1)
          & r2_hidden(sK12(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f27,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK12(X0,X1),X1)
        & r2_hidden(sK12(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f317,plain,(
    ! [X0] : k7_relat_1(k1_xboole_0,X0) = k7_relat_1(sK2,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f96,f290])).

fof(f188,plain,(
    ! [X8] : k2_relat_1(k7_relat_1(k1_xboole_0,X8)) = k9_relat_1(k1_xboole_0,X8) ),
    inference(resolution,[],[f140,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f135,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(k1_xboole_0,X3))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f111,f88])).

fof(f88,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f346,plain,(
    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f126,f318])).

fof(f318,plain,(
    k9_relat_1(sK2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f95,f290])).

fof(f95,plain,(
    ! [X8] : k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8) ),
    inference(resolution,[],[f56,f78])).

fof(f126,plain,(
    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f125,f108])).

fof(f125,plain,(
    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f116,f104])).

fof(f104,plain,(
    ! [X14,X13] : k9_relat_1(sK2,k3_xboole_0(X13,X14)) = k3_xboole_0(k9_relat_1(sK2,X13),k9_relat_1(sK2,X14)) ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    ! [X14,X13] :
      ( k9_relat_1(sK2,k3_xboole_0(X13,X14)) = k3_xboole_0(k9_relat_1(sK2,X13),k9_relat_1(sK2,X14))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f98,f59])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    ! [X14,X13] :
      ( k9_relat_1(sK2,k3_xboole_0(X13,X14)) = k3_xboole_0(k9_relat_1(sK2,X13),k9_relat_1(sK2,X14))
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f56,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f116,plain,(
    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f60,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f60,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:46:34 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.41  % (26367)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.43  % (26361)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.43  % (26376)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.44  % (26362)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.44  % (26366)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.18/0.45  % (26361)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f355,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(subsumption_resolution,[],[f346,f339])).
% 0.18/0.45  fof(f339,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0))) )),
% 0.18/0.45    inference(subsumption_resolution,[],[f329,f140])).
% 0.18/0.45  fof(f140,plain,(
% 0.18/0.45    v1_relat_1(k1_xboole_0)),
% 0.18/0.45    inference(resolution,[],[f111,f71])).
% 0.18/0.45  fof(f71,plain,(
% 0.18/0.45    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK8(X0),X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f50])).
% 0.18/0.45  fof(f50,plain,(
% 0.18/0.45    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK8(X0) & r2_hidden(sK8(X0),X0))) & (! [X4] : (k4_tarski(sK9(X4),sK10(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f47,f49,f48])).
% 0.18/0.45  fof(f48,plain,(
% 0.18/0.45    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK8(X0) & r2_hidden(sK8(X0),X0)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f49,plain,(
% 0.18/0.45    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK9(X4),sK10(X4)) = X4)),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f47,plain,(
% 0.18/0.45    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.18/0.45    inference(rectify,[],[f46])).
% 0.18/0.45  fof(f46,plain,(
% 0.18/0.45    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.18/0.45    inference(nnf_transformation,[],[f25])).
% 0.18/0.45  % (26359)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.45  fof(f25,plain,(
% 0.18/0.45    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f8])).
% 0.18/0.45  fof(f8,axiom,(
% 0.18/0.45    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.18/0.45  fof(f111,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.18/0.45    inference(forward_demodulation,[],[f110,f108])).
% 0.18/0.45  fof(f108,plain,(
% 0.18/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.18/0.45    inference(resolution,[],[f58,f79])).
% 0.18/0.45  fof(f79,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f55])).
% 0.18/0.45  fof(f55,plain,(
% 0.18/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(nnf_transformation,[],[f1])).
% 0.18/0.45  fof(f1,axiom,(
% 0.18/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.18/0.45  fof(f58,plain,(
% 0.18/0.45    r1_xboole_0(sK0,sK1)),
% 0.18/0.45    inference(cnf_transformation,[],[f37])).
% 0.18/0.45  fof(f37,plain,(
% 0.18/0.45    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).
% 0.18/0.45  fof(f36,plain,(
% 0.18/0.45    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f20,plain,(
% 0.18/0.45    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.18/0.45    inference(flattening,[],[f19])).
% 0.18/0.45  fof(f19,plain,(
% 0.18/0.45    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.18/0.45    inference(ennf_transformation,[],[f16])).
% 0.18/0.45  fof(f16,negated_conjecture,(
% 0.18/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.18/0.45    inference(negated_conjecture,[],[f15])).
% 0.18/0.45  fof(f15,conjecture,(
% 0.18/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.18/0.45  fof(f110,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK0,sK1))) )),
% 0.18/0.45    inference(resolution,[],[f58,f74])).
% 0.18/0.45  fof(f74,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.18/0.45    inference(cnf_transformation,[],[f52])).
% 0.18/0.45  fof(f52,plain,(
% 0.18/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK11(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f26,f51])).
% 0.18/0.45  fof(f51,plain,(
% 0.18/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK11(X0,X1),k3_xboole_0(X0,X1)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f26,plain,(
% 0.18/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(ennf_transformation,[],[f17])).
% 0.18/0.45  fof(f17,plain,(
% 0.18/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(rectify,[],[f3])).
% 0.18/0.45  fof(f3,axiom,(
% 0.18/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.18/0.45  fof(f329,plain,(
% 0.18/0.45    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.18/0.45    inference(backward_demodulation,[],[f135,f325])).
% 0.18/0.45  fof(f325,plain,(
% 0.18/0.45    ( ! [X8] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X8)) )),
% 0.18/0.45    inference(backward_demodulation,[],[f188,f323])).
% 0.18/0.45  fof(f323,plain,(
% 0.18/0.45    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.18/0.45    inference(forward_demodulation,[],[f322,f290])).
% 0.18/0.45  fof(f290,plain,(
% 0.18/0.45    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.18/0.45    inference(forward_demodulation,[],[f287,f108])).
% 0.18/0.45  fof(f287,plain,(
% 0.18/0.45    k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.18/0.45    inference(resolution,[],[f102,f58])).
% 0.18/0.45  fof(f102,plain,(
% 0.18/0.45    ( ! [X12,X11] : (~r1_xboole_0(X11,X12) | k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X11,X12))) )),
% 0.18/0.45    inference(forward_demodulation,[],[f97,f96])).
% 0.18/0.45  fof(f96,plain,(
% 0.18/0.45    ( ! [X10,X9] : (k7_relat_1(k7_relat_1(sK2,X9),X10) = k7_relat_1(sK2,k3_xboole_0(X9,X10))) )),
% 0.18/0.45    inference(resolution,[],[f56,f83])).
% 0.18/0.45  fof(f83,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f31])).
% 0.18/0.45  fof(f31,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(ennf_transformation,[],[f9])).
% 0.18/0.45  fof(f9,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.18/0.45  fof(f56,plain,(
% 0.18/0.45    v1_relat_1(sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f37])).
% 0.18/0.45  fof(f97,plain,(
% 0.18/0.45    ( ! [X12,X11] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X11),X12) | ~r1_xboole_0(X11,X12)) )),
% 0.18/0.45    inference(resolution,[],[f56,f84])).
% 0.18/0.45  fof(f84,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f33])).
% 0.18/0.45  fof(f33,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(flattening,[],[f32])).
% 0.18/0.45  fof(f32,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(ennf_transformation,[],[f12])).
% 0.18/0.45  fof(f12,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.18/0.45  % (26369)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.45  fof(f322,plain,(
% 0.18/0.45    ( ! [X0] : (k7_relat_1(k1_xboole_0,X0) = k7_relat_1(sK2,k1_xboole_0)) )),
% 0.18/0.45    inference(forward_demodulation,[],[f317,f224])).
% 0.18/0.45  fof(f224,plain,(
% 0.18/0.45    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.18/0.45    inference(resolution,[],[f142,f79])).
% 0.18/0.45  fof(f142,plain,(
% 0.18/0.45    ( ! [X13] : (r1_xboole_0(k1_xboole_0,X13)) )),
% 0.18/0.45    inference(resolution,[],[f111,f75])).
% 0.18/0.45  fof(f75,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r2_hidden(sK12(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f54])).
% 0.18/0.45  fof(f54,plain,(
% 0.18/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK12(X0,X1),X1) & r2_hidden(sK12(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f27,f53])).
% 0.18/0.45  fof(f53,plain,(
% 0.18/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK12(X0,X1),X1) & r2_hidden(sK12(X0,X1),X0)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f27,plain,(
% 0.18/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(ennf_transformation,[],[f18])).
% 0.18/0.45  fof(f18,plain,(
% 0.18/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.45    inference(rectify,[],[f2])).
% 0.18/0.45  fof(f2,axiom,(
% 0.18/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.18/0.45  fof(f317,plain,(
% 0.18/0.45    ( ! [X0] : (k7_relat_1(k1_xboole_0,X0) = k7_relat_1(sK2,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.18/0.45    inference(superposition,[],[f96,f290])).
% 0.18/0.45  fof(f188,plain,(
% 0.18/0.45    ( ! [X8] : (k2_relat_1(k7_relat_1(k1_xboole_0,X8)) = k9_relat_1(k1_xboole_0,X8)) )),
% 0.18/0.45    inference(resolution,[],[f140,f78])).
% 0.18/0.45  fof(f78,plain,(
% 0.18/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f28])).
% 0.18/0.45  fof(f28,plain,(
% 0.18/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.45    inference(ennf_transformation,[],[f11])).
% 0.18/0.45  fof(f11,axiom,(
% 0.18/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.18/0.45  fof(f135,plain,(
% 0.18/0.45    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(k1_xboole_0,X3)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.18/0.45    inference(resolution,[],[f111,f88])).
% 0.18/0.45  fof(f88,plain,(
% 0.18/0.45    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(equality_resolution,[],[f64])).
% 0.18/0.45  fof(f64,plain,(
% 0.18/0.45    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f45])).
% 0.18/0.45  fof(f45,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f41,f44,f43,f42])).
% 0.18/0.45  fof(f42,plain,(
% 0.18/0.45    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f43,plain,(
% 0.18/0.45    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0)) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f44,plain,(
% 0.18/0.45    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X0)))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f41,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(rectify,[],[f40])).
% 0.18/0.45  fof(f40,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(nnf_transformation,[],[f24])).
% 0.18/0.45  fof(f24,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(ennf_transformation,[],[f7])).
% 0.18/0.45  fof(f7,axiom,(
% 0.18/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.18/0.45  fof(f346,plain,(
% 0.18/0.45    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k2_relat_1(k1_xboole_0))),
% 0.18/0.45    inference(backward_demodulation,[],[f126,f318])).
% 0.18/0.45  fof(f318,plain,(
% 0.18/0.45    k9_relat_1(sK2,k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 0.18/0.45    inference(superposition,[],[f95,f290])).
% 0.18/0.45  fof(f95,plain,(
% 0.18/0.45    ( ! [X8] : (k2_relat_1(k7_relat_1(sK2,X8)) = k9_relat_1(sK2,X8)) )),
% 0.18/0.45    inference(resolution,[],[f56,f78])).
% 0.18/0.45  fof(f126,plain,(
% 0.18/0.45    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_xboole_0))),
% 0.18/0.45    inference(forward_demodulation,[],[f125,f108])).
% 0.18/0.45  fof(f125,plain,(
% 0.18/0.45    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 0.18/0.45    inference(forward_demodulation,[],[f116,f104])).
% 0.18/0.45  fof(f104,plain,(
% 0.18/0.45    ( ! [X14,X13] : (k9_relat_1(sK2,k3_xboole_0(X13,X14)) = k3_xboole_0(k9_relat_1(sK2,X13),k9_relat_1(sK2,X14))) )),
% 0.18/0.45    inference(subsumption_resolution,[],[f103,f57])).
% 0.18/0.45  fof(f57,plain,(
% 0.18/0.45    v1_funct_1(sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f37])).
% 0.18/0.45  fof(f103,plain,(
% 0.18/0.45    ( ! [X14,X13] : (k9_relat_1(sK2,k3_xboole_0(X13,X14)) = k3_xboole_0(k9_relat_1(sK2,X13),k9_relat_1(sK2,X14)) | ~v1_funct_1(sK2)) )),
% 0.18/0.45    inference(subsumption_resolution,[],[f98,f59])).
% 0.18/0.45  fof(f59,plain,(
% 0.18/0.45    v2_funct_1(sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f37])).
% 0.18/0.45  fof(f98,plain,(
% 0.18/0.45    ( ! [X14,X13] : (k9_relat_1(sK2,k3_xboole_0(X13,X14)) = k3_xboole_0(k9_relat_1(sK2,X13),k9_relat_1(sK2,X14)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2)) )),
% 0.18/0.45    inference(resolution,[],[f56,f85])).
% 0.18/0.45  fof(f85,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f35])).
% 0.18/0.45  fof(f35,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(flattening,[],[f34])).
% 0.18/0.45  fof(f34,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.18/0.45    inference(ennf_transformation,[],[f14])).
% 0.18/0.45  fof(f14,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.18/0.45  fof(f116,plain,(
% 0.18/0.45    r2_hidden(sK11(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.18/0.45    inference(resolution,[],[f60,f73])).
% 0.18/0.45  fof(f73,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f52])).
% 0.18/0.45  fof(f60,plain,(
% 0.18/0.45    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.18/0.45    inference(cnf_transformation,[],[f37])).
% 0.18/0.45  % SZS output end Proof for theBenchmark
% 0.18/0.45  % (26361)------------------------------
% 0.18/0.45  % (26361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (26361)Termination reason: Refutation
% 0.18/0.45  
% 0.18/0.45  % (26361)Memory used [KB]: 1918
% 0.18/0.45  % (26361)Time elapsed: 0.060 s
% 0.18/0.45  % (26361)------------------------------
% 0.18/0.45  % (26361)------------------------------
% 0.18/0.45  % (26355)Success in time 0.116 s
%------------------------------------------------------------------------------
