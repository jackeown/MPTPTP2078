%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0711+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:31 EST 2020

% Result     : Theorem 6.47s
% Output     : Refutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 560 expanded)
%              Number of leaves         :   12 ( 199 expanded)
%              Depth                    :   24
%              Number of atoms          :  404 (3853 expanded)
%              Number of equality atoms :  135 (1557 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10327,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10326,f36])).

fof(f36,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(f10326,plain,(
    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f10321])).

fof(f10321,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(resolution,[],[f10320,f5913])).

fof(f5913,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k7_relat_1(sK1,X1),k7_relat_1(sK0,X1)),X1)
      | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) ) ),
    inference(resolution,[],[f2179,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2179,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k7_relat_1(sK1,X0),k7_relat_1(sK0,X0)),k3_xboole_0(k1_relat_1(sK0),X0))
      | k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0) ) ),
    inference(equality_resolution,[],[f754])).

fof(f754,plain,(
    ! [X12,X11] :
      ( k3_xboole_0(k1_relat_1(sK0),X11) != k3_xboole_0(k1_relat_1(sK0),X12)
      | k7_relat_1(sK0,X12) = k7_relat_1(sK1,X11)
      | r2_hidden(sK3(k7_relat_1(sK1,X11),k7_relat_1(sK0,X12)),k3_xboole_0(k1_relat_1(sK0),X11)) ) ),
    inference(subsumption_resolution,[],[f753,f79])).

fof(f79,plain,(
    ! [X4] : v1_relat_1(k7_relat_1(sK1,X4)) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f753,plain,(
    ! [X12,X11] :
      ( k3_xboole_0(k1_relat_1(sK0),X11) != k3_xboole_0(k1_relat_1(sK0),X12)
      | k7_relat_1(sK0,X12) = k7_relat_1(sK1,X11)
      | r2_hidden(sK3(k7_relat_1(sK1,X11),k7_relat_1(sK0,X12)),k3_xboole_0(k1_relat_1(sK0),X11))
      | ~ v1_relat_1(k7_relat_1(sK1,X11)) ) ),
    inference(subsumption_resolution,[],[f745,f95])).

fof(f95,plain,(
    ! [X5] : v1_funct_1(k7_relat_1(sK1,X5)) ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f89,plain,(
    ! [X5] :
      ( v1_funct_1(k7_relat_1(sK1,X5))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f745,plain,(
    ! [X12,X11] :
      ( k3_xboole_0(k1_relat_1(sK0),X11) != k3_xboole_0(k1_relat_1(sK0),X12)
      | k7_relat_1(sK0,X12) = k7_relat_1(sK1,X11)
      | r2_hidden(sK3(k7_relat_1(sK1,X11),k7_relat_1(sK0,X12)),k3_xboole_0(k1_relat_1(sK0),X11))
      | ~ v1_funct_1(k7_relat_1(sK1,X11))
      | ~ v1_relat_1(k7_relat_1(sK1,X11)) ) ),
    inference(superposition,[],[f175,f182])).

fof(f182,plain,(
    ! [X5] : k3_xboole_0(k1_relat_1(sK0),X5) = k1_relat_1(k7_relat_1(sK1,X5)) ),
    inference(forward_demodulation,[],[f80,f34])).

fof(f34,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X5] : k1_relat_1(k7_relat_1(sK1,X5)) = k3_xboole_0(k1_relat_1(sK1),X5) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f175,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(k1_relat_1(sK0),X5) != k1_relat_1(X6)
      | k7_relat_1(sK0,X5) = X6
      | r2_hidden(sK3(X6,k7_relat_1(sK0,X5)),k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f57,plain,(
    ! [X4] : v1_relat_1(k7_relat_1(sK0,X4)) ),
    inference(resolution,[],[f30,f39])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f174,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(k1_relat_1(sK0),X5) != k1_relat_1(X6)
      | k7_relat_1(sK0,X5) = X6
      | r2_hidden(sK3(X6,k7_relat_1(sK0,X5)),k1_relat_1(X6))
      | ~ v1_relat_1(k7_relat_1(sK0,X5))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f166,f73])).

fof(f73,plain,(
    ! [X5] : v1_funct_1(k7_relat_1(sK0,X5)) ),
    inference(subsumption_resolution,[],[f67,f30])).

fof(f67,plain,(
    ! [X5] :
      ( v1_funct_1(k7_relat_1(sK0,X5))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f31,f42])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f166,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(k1_relat_1(sK0),X5) != k1_relat_1(X6)
      | k7_relat_1(sK0,X5) = X6
      | r2_hidden(sK3(X6,k7_relat_1(sK0,X5)),k1_relat_1(X6))
      | ~ v1_funct_1(k7_relat_1(sK0,X5))
      | ~ v1_relat_1(k7_relat_1(sK0,X5))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f37,f58])).

fof(f58,plain,(
    ! [X5] : k1_relat_1(k7_relat_1(sK0,X5)) = k3_xboole_0(k1_relat_1(sK0),X5) ),
    inference(resolution,[],[f30,f40])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f10320,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k7_relat_1(sK1,X0),k7_relat_1(sK0,X0)),sK2)
      | k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f10314,f2179])).

fof(f10314,plain,(
    ! [X0] :
      ( k7_relat_1(sK0,X0) = k7_relat_1(sK1,X0)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X0),k7_relat_1(sK0,X0)),sK2)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X0),k7_relat_1(sK0,X0)),k3_xboole_0(k1_relat_1(sK0),X0)) ) ),
    inference(equality_resolution,[],[f3504])).

fof(f3504,plain,(
    ! [X10,X9] :
      ( k3_xboole_0(k1_relat_1(sK0),X9) != k3_xboole_0(k1_relat_1(sK0),X10)
      | k7_relat_1(sK1,X10) = k7_relat_1(sK0,X9)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),sK2)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),k3_xboole_0(k1_relat_1(sK0),X9)) ) ),
    inference(forward_demodulation,[],[f3503,f58])).

fof(f3503,plain,(
    ! [X10,X9] :
      ( k1_relat_1(k7_relat_1(sK0,X9)) != k3_xboole_0(k1_relat_1(sK0),X10)
      | k7_relat_1(sK1,X10) = k7_relat_1(sK0,X9)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),sK2)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),k3_xboole_0(k1_relat_1(sK0),X9)) ) ),
    inference(subsumption_resolution,[],[f3502,f57])).

fof(f3502,plain,(
    ! [X10,X9] :
      ( k1_relat_1(k7_relat_1(sK0,X9)) != k3_xboole_0(k1_relat_1(sK0),X10)
      | k7_relat_1(sK1,X10) = k7_relat_1(sK0,X9)
      | ~ v1_relat_1(k7_relat_1(sK0,X9))
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),sK2)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),k3_xboole_0(k1_relat_1(sK0),X9)) ) ),
    inference(subsumption_resolution,[],[f3493,f73])).

fof(f3493,plain,(
    ! [X10,X9] :
      ( k1_relat_1(k7_relat_1(sK0,X9)) != k3_xboole_0(k1_relat_1(sK0),X10)
      | k7_relat_1(sK1,X10) = k7_relat_1(sK0,X9)
      | ~ v1_funct_1(k7_relat_1(sK0,X9))
      | ~ v1_relat_1(k7_relat_1(sK0,X9))
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),sK2)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),k3_xboole_0(k1_relat_1(sK0),X9)) ) ),
    inference(trivial_inequality_removal,[],[f3484])).

fof(f3484,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK0,sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9))) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)))
      | k1_relat_1(k7_relat_1(sK0,X9)) != k3_xboole_0(k1_relat_1(sK0),X10)
      | k7_relat_1(sK1,X10) = k7_relat_1(sK0,X9)
      | ~ v1_funct_1(k7_relat_1(sK0,X9))
      | ~ v1_relat_1(k7_relat_1(sK0,X9))
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),sK2)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X10),k7_relat_1(sK0,X9)),k3_xboole_0(k1_relat_1(sK0),X9)) ) ),
    inference(superposition,[],[f1238,f214])).

fof(f214,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k7_relat_1(sK0,X6),X7) = k1_funct_1(sK0,X7)
      | ~ r2_hidden(X7,k3_xboole_0(k1_relat_1(sK0),X6)) ) ),
    inference(forward_demodulation,[],[f74,f58])).

fof(f74,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k7_relat_1(sK0,X6),X7) = k1_funct_1(sK0,X7)
      | ~ r2_hidden(X7,k1_relat_1(k7_relat_1(sK0,X6))) ) ),
    inference(subsumption_resolution,[],[f68,f30])).

fof(f68,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k7_relat_1(sK0,X6),X7) = k1_funct_1(sK0,X7)
      | ~ r2_hidden(X7,k1_relat_1(k7_relat_1(sK0,X6)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f1238,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK3(k7_relat_1(sK1,X0),X1)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,X0),X1))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(sK0),X0)
      | k7_relat_1(sK1,X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X0),X1),sK2) ) ),
    inference(superposition,[],[f1225,f35])).

fof(f35,plain,(
    ! [X3] :
      ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1225,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,sK3(k7_relat_1(sK1,X2),X3)) != k1_funct_1(X3,sK3(k7_relat_1(sK1,X2),X3))
      | k1_relat_1(X3) != k3_xboole_0(k1_relat_1(sK0),X2)
      | k7_relat_1(sK1,X2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f241,f205])).

fof(f205,plain,(
    ! [X4,X3] :
      ( k1_relat_1(X4) != k3_xboole_0(k1_relat_1(sK0),X3)
      | k7_relat_1(sK1,X3) = X4
      | r2_hidden(sK3(k7_relat_1(sK1,X3),X4),k3_xboole_0(k1_relat_1(sK0),X3))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f204,f79])).

fof(f204,plain,(
    ! [X4,X3] :
      ( k1_relat_1(X4) != k3_xboole_0(k1_relat_1(sK0),X3)
      | k7_relat_1(sK1,X3) = X4
      | r2_hidden(sK3(k7_relat_1(sK1,X3),X4),k3_xboole_0(k1_relat_1(sK0),X3))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k7_relat_1(sK1,X3)) ) ),
    inference(subsumption_resolution,[],[f195,f95])).

fof(f195,plain,(
    ! [X4,X3] :
      ( k1_relat_1(X4) != k3_xboole_0(k1_relat_1(sK0),X3)
      | k7_relat_1(sK1,X3) = X4
      | r2_hidden(sK3(k7_relat_1(sK1,X3),X4),k3_xboole_0(k1_relat_1(sK0),X3))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(k7_relat_1(sK1,X3))
      | ~ v1_relat_1(k7_relat_1(sK1,X3)) ) ),
    inference(superposition,[],[f37,f182])).

fof(f241,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X3) != k3_xboole_0(k1_relat_1(sK0),X2)
      | k1_funct_1(sK1,sK3(k7_relat_1(sK1,X2),X3)) != k1_funct_1(X3,sK3(k7_relat_1(sK1,X2),X3))
      | k7_relat_1(sK1,X2) = X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X2),X3),k3_xboole_0(k1_relat_1(sK0),X2)) ) ),
    inference(forward_demodulation,[],[f240,f182])).

fof(f240,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,sK3(k7_relat_1(sK1,X2),X3)) != k1_funct_1(X3,sK3(k7_relat_1(sK1,X2),X3))
      | k7_relat_1(sK1,X2) = X3
      | k1_relat_1(X3) != k1_relat_1(k7_relat_1(sK1,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X2),X3),k3_xboole_0(k1_relat_1(sK0),X2)) ) ),
    inference(subsumption_resolution,[],[f239,f79])).

fof(f239,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,sK3(k7_relat_1(sK1,X2),X3)) != k1_funct_1(X3,sK3(k7_relat_1(sK1,X2),X3))
      | k7_relat_1(sK1,X2) = X3
      | k1_relat_1(X3) != k1_relat_1(k7_relat_1(sK1,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(sK1,X2))
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X2),X3),k3_xboole_0(k1_relat_1(sK0),X2)) ) ),
    inference(subsumption_resolution,[],[f237,f95])).

fof(f237,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,sK3(k7_relat_1(sK1,X2),X3)) != k1_funct_1(X3,sK3(k7_relat_1(sK1,X2),X3))
      | k7_relat_1(sK1,X2) = X3
      | k1_relat_1(X3) != k1_relat_1(k7_relat_1(sK1,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(k7_relat_1(sK1,X2))
      | ~ v1_relat_1(k7_relat_1(sK1,X2))
      | ~ r2_hidden(sK3(k7_relat_1(sK1,X2),X3),k3_xboole_0(k1_relat_1(sK0),X2)) ) ),
    inference(superposition,[],[f38,f215])).

fof(f215,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k7_relat_1(sK1,X6),X7) = k1_funct_1(sK1,X7)
      | ~ r2_hidden(X7,k3_xboole_0(k1_relat_1(sK0),X6)) ) ),
    inference(forward_demodulation,[],[f96,f182])).

fof(f96,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k7_relat_1(sK1,X6),X7) = k1_funct_1(sK1,X7)
      | ~ r2_hidden(X7,k1_relat_1(k7_relat_1(sK1,X6))) ) ),
    inference(subsumption_resolution,[],[f90,f32])).

fof(f90,plain,(
    ! [X6,X7] :
      ( k1_funct_1(k7_relat_1(sK1,X6),X7) = k1_funct_1(sK1,X7)
      | ~ r2_hidden(X7,k1_relat_1(k7_relat_1(sK1,X6)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f33,f43])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
