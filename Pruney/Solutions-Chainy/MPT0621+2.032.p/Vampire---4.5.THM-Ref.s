%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 448 expanded)
%              Number of leaves         :   10 ( 134 expanded)
%              Depth                    :   23
%              Number of atoms          :  282 (2168 expanded)
%              Number of equality atoms :  148 (1017 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f616,plain,(
    $false ),
    inference(subsumption_resolution,[],[f615,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f615,plain,(
    k1_xboole_0 = sK0 ),
    inference(condensation,[],[f550])).

fof(f550,plain,(
    ! [X4,X3] :
      ( X3 = X4
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f540,f508])).

fof(f508,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK4(X0,X1),sK1(k1_xboole_0,X0)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f507])).

fof(f507,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(sK4(X0,X1),sK1(k1_xboole_0,X0)) = X1
      | k1_xboole_0 = X0
      | k1_funct_1(sK4(X0,X2),sK1(k1_xboole_0,X0)) = X2 ) ),
    inference(condensation,[],[f506])).

fof(f506,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 = X2
      | k1_funct_1(sK4(X0,X3),sK1(k1_xboole_0,X0)) = X3
      | k1_xboole_0 = X0
      | k1_funct_1(sK4(X0,X4),sK1(k1_xboole_0,X0)) = X4 ) ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 = X2
      | k1_funct_1(sK4(X0,X3),sK1(k1_xboole_0,X0)) = X3
      | k1_xboole_0 = X0
      | k1_funct_1(sK4(X0,X4),sK1(k1_xboole_0,X0)) = X4
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f202,f202])).

fof(f202,plain,(
    ! [X8,X7,X9] :
      ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X7)) = X8
      | k1_funct_1(sK4(X7,X9),sK1(k1_xboole_0,X7)) = X9
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f157,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK4(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f157,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK1(k1_xboole_0,X10),X10)
      | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X10)) = X11
      | k1_xboole_0 = X10 ) ),
    inference(forward_demodulation,[],[f143,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = sK4(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK4(X0,X1) ) ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(sK4(X0,X1))
      | k1_xboole_0 = sK4(X0,X1) ) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f143,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK1(k1_xboole_0,X10),X10)
      | k1_xboole_0 = X10
      | k1_funct_1(sK4(k1_xboole_0,X11),sK2(k1_xboole_0,X10)) = X11 ) ),
    inference(resolution,[],[f136,f39])).

fof(f136,plain,(
    ! [X3] :
      ( r2_hidden(sK2(k1_xboole_0,X3),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f135,f27])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f135,plain,(
    ! [X3] :
      ( r2_hidden(sK2(k1_xboole_0,X3),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,X3),X3)
      | k2_relat_1(k1_xboole_0) = X3 ) ),
    inference(forward_demodulation,[],[f134,f26])).

fof(f26,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f134,plain,(
    ! [X3] :
      ( r2_hidden(sK2(k1_xboole_0,X3),k1_relat_1(k1_xboole_0))
      | r2_hidden(sK1(k1_xboole_0,X3),X3)
      | k2_relat_1(k1_xboole_0) = X3 ) ),
    inference(subsumption_resolution,[],[f131,f51])).

fof(f51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f36,f47])).

fof(f131,plain,(
    ! [X3] :
      ( r2_hidden(sK2(k1_xboole_0,X3),k1_relat_1(k1_xboole_0))
      | r2_hidden(sK1(k1_xboole_0,X3),X3)
      | k2_relat_1(k1_xboole_0) = X3
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f37,f47])).

fof(f37,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK1(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f540,plain,(
    ! [X2,X1] : k1_funct_1(sK4(sK0,X2),sK1(k1_xboole_0,sK0)) = X1 ),
    inference(subsumption_resolution,[],[f537,f25])).

fof(f537,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK4(sK0,X2),sK1(k1_xboole_0,sK0)) = X1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f508,f109])).

% (5836)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f109,plain,(
    ! [X0,X1] : sK4(sK0,X1) = sK4(sK0,X0) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK4(X0,X1) = sK4(sK0,X2) ) ),
    inference(superposition,[],[f105,f38])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sK0 != k1_relat_1(sK4(X0,X1))
      | sK4(X0,X1) = sK4(sK0,X2) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X2
      | sK0 != k1_relat_1(sK4(X0,X1))
      | sK4(X0,X1) = sK4(X2,X3) ) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != k1_relat_1(sK4(X0,X1))
      | sK0 != X2
      | ~ v1_relat_1(sK4(X0,X1))
      | sK4(X0,X1) = sK4(X2,X3) ) ),
    inference(resolution,[],[f97,f37])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | sK0 != X1
      | ~ v1_relat_1(X0)
      | sK4(X1,X2) = X0 ) ),
    inference(forward_demodulation,[],[f96,f38])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK4(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X1,X2) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK4(X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X1,X2) = X0
      | ~ v1_relat_1(sK4(X1,X2)) ) ),
    inference(resolution,[],[f24,f37])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.47  % (5844)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (5832)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.49  % (5839)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.49  % (5838)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (5852)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.49  % (5833)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  % (5848)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (5843)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (5837)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.50  % (5835)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.50  % (5835)Refutation not found, incomplete strategy% (5835)------------------------------
% 0.19/0.50  % (5835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (5835)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (5835)Memory used [KB]: 6140
% 0.19/0.50  % (5835)Time elapsed: 0.096 s
% 0.19/0.50  % (5835)------------------------------
% 0.19/0.50  % (5835)------------------------------
% 0.19/0.50  % (5837)Refutation not found, incomplete strategy% (5837)------------------------------
% 0.19/0.50  % (5837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (5851)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.50  % (5843)Refutation not found, incomplete strategy% (5843)------------------------------
% 0.19/0.50  % (5843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (5845)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.51  % (5843)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (5843)Memory used [KB]: 6012
% 0.19/0.51  % (5843)Time elapsed: 0.097 s
% 0.19/0.51  % (5843)------------------------------
% 0.19/0.51  % (5843)------------------------------
% 0.19/0.51  % (5849)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (5837)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (5837)Memory used [KB]: 1663
% 0.19/0.51  % (5837)Time elapsed: 0.099 s
% 0.19/0.51  % (5837)------------------------------
% 0.19/0.51  % (5837)------------------------------
% 0.19/0.51  % (5854)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.51  % (5830)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (5830)Refutation not found, incomplete strategy% (5830)------------------------------
% 0.19/0.51  % (5830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (5830)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (5830)Memory used [KB]: 10490
% 0.19/0.51  % (5830)Time elapsed: 0.107 s
% 0.19/0.51  % (5830)------------------------------
% 0.19/0.51  % (5830)------------------------------
% 0.19/0.51  % (5855)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.51  % (5841)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.51  % (5834)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.51  % (5846)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.51  % (5841)Refutation not found, incomplete strategy% (5841)------------------------------
% 0.19/0.51  % (5841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (5841)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (5841)Memory used [KB]: 10490
% 0.19/0.51  % (5841)Time elapsed: 0.111 s
% 0.19/0.51  % (5841)------------------------------
% 0.19/0.51  % (5841)------------------------------
% 0.19/0.52  % (5851)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f616,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(subsumption_resolution,[],[f615,f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    k1_xboole_0 != sK0),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f8,plain,(
% 0.19/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(flattening,[],[f7])).
% 0.19/0.52  fof(f7,plain,(
% 0.19/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,negated_conjecture,(
% 0.19/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.19/0.52    inference(negated_conjecture,[],[f5])).
% 0.19/0.52  fof(f5,conjecture,(
% 0.19/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.19/0.52  fof(f615,plain,(
% 0.19/0.52    k1_xboole_0 = sK0),
% 0.19/0.52    inference(condensation,[],[f550])).
% 0.19/0.52  fof(f550,plain,(
% 0.19/0.52    ( ! [X4,X3] : (X3 = X4 | k1_xboole_0 = sK0) )),
% 0.19/0.52    inference(superposition,[],[f540,f508])).
% 0.19/0.52  fof(f508,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_funct_1(sK4(X0,X1),sK1(k1_xboole_0,X0)) = X1 | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(condensation,[],[f507])).
% 0.19/0.52  fof(f507,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k1_funct_1(sK4(X0,X1),sK1(k1_xboole_0,X0)) = X1 | k1_xboole_0 = X0 | k1_funct_1(sK4(X0,X2),sK1(k1_xboole_0,X0)) = X2) )),
% 0.19/0.52    inference(condensation,[],[f506])).
% 0.19/0.52  fof(f506,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X3,X1] : (X1 = X2 | k1_funct_1(sK4(X0,X3),sK1(k1_xboole_0,X0)) = X3 | k1_xboole_0 = X0 | k1_funct_1(sK4(X0,X4),sK1(k1_xboole_0,X0)) = X4) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f409])).
% 0.19/0.52  fof(f409,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X3,X1] : (X1 = X2 | k1_funct_1(sK4(X0,X3),sK1(k1_xboole_0,X0)) = X3 | k1_xboole_0 = X0 | k1_funct_1(sK4(X0,X4),sK1(k1_xboole_0,X0)) = X4 | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(superposition,[],[f202,f202])).
% 0.19/0.52  fof(f202,plain,(
% 0.19/0.52    ( ! [X8,X7,X9] : (k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X7)) = X8 | k1_funct_1(sK4(X7,X9),sK1(k1_xboole_0,X7)) = X9 | k1_xboole_0 = X7) )),
% 0.19/0.52    inference(resolution,[],[f157,f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK4(X0,X1),X3) = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f13,plain,(
% 0.19/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.19/0.52  fof(f157,plain,(
% 0.19/0.52    ( ! [X10,X11] : (r2_hidden(sK1(k1_xboole_0,X10),X10) | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X10)) = X11 | k1_xboole_0 = X10) )),
% 0.19/0.52    inference(forward_demodulation,[],[f143,f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X0] : (k1_xboole_0 = sK4(k1_xboole_0,X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK4(X0,X1)) )),
% 0.19/0.52    inference(superposition,[],[f44,f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK4(X0,X1)) | k1_xboole_0 = sK4(X0,X1)) )),
% 0.19/0.52    inference(resolution,[],[f28,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,plain,(
% 0.19/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(flattening,[],[f9])).
% 0.19/0.52  fof(f9,plain,(
% 0.19/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.52  fof(f143,plain,(
% 0.19/0.52    ( ! [X10,X11] : (r2_hidden(sK1(k1_xboole_0,X10),X10) | k1_xboole_0 = X10 | k1_funct_1(sK4(k1_xboole_0,X11),sK2(k1_xboole_0,X10)) = X11) )),
% 0.19/0.52    inference(resolution,[],[f136,f39])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    ( ! [X3] : (r2_hidden(sK2(k1_xboole_0,X3),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X3),X3) | k1_xboole_0 = X3) )),
% 0.19/0.52    inference(forward_demodulation,[],[f135,f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.52    inference(cnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    ( ! [X3] : (r2_hidden(sK2(k1_xboole_0,X3),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X3),X3) | k2_relat_1(k1_xboole_0) = X3) )),
% 0.19/0.52    inference(forward_demodulation,[],[f134,f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.52    inference(cnf_transformation,[],[f1])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    ( ! [X3] : (r2_hidden(sK2(k1_xboole_0,X3),k1_relat_1(k1_xboole_0)) | r2_hidden(sK1(k1_xboole_0,X3),X3) | k2_relat_1(k1_xboole_0) = X3) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f131,f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    v1_relat_1(k1_xboole_0)),
% 0.19/0.52    inference(superposition,[],[f36,f47])).
% 0.19/0.52  fof(f131,plain,(
% 0.19/0.52    ( ! [X3] : (r2_hidden(sK2(k1_xboole_0,X3),k1_relat_1(k1_xboole_0)) | r2_hidden(sK1(k1_xboole_0,X3),X3) | k2_relat_1(k1_xboole_0) = X3 | ~v1_relat_1(k1_xboole_0)) )),
% 0.19/0.52    inference(resolution,[],[f33,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    v1_funct_1(k1_xboole_0)),
% 0.19/0.52    inference(superposition,[],[f37,f47])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f20,f19,f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(rectify,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(flattening,[],[f11])).
% 0.19/0.52  fof(f11,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.19/0.52  fof(f540,plain,(
% 0.19/0.52    ( ! [X2,X1] : (k1_funct_1(sK4(sK0,X2),sK1(k1_xboole_0,sK0)) = X1) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f537,f25])).
% 0.19/0.52  fof(f537,plain,(
% 0.19/0.52    ( ! [X2,X1] : (k1_funct_1(sK4(sK0,X2),sK1(k1_xboole_0,sK0)) = X1 | k1_xboole_0 = sK0) )),
% 0.19/0.52    inference(superposition,[],[f508,f109])).
% 0.19/0.52  % (5836)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    ( ! [X0,X1] : (sK4(sK0,X1) = sK4(sK0,X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f107])).
% 0.19/0.52  fof(f107,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (sK0 != X0 | sK4(X0,X1) = sK4(sK0,X2)) )),
% 0.19/0.52    inference(superposition,[],[f105,f38])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (sK0 != k1_relat_1(sK4(X0,X1)) | sK4(X0,X1) = sK4(sK0,X2)) )),
% 0.19/0.52    inference(equality_resolution,[],[f102])).
% 0.19/0.52  fof(f102,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (sK0 != X2 | sK0 != k1_relat_1(sK4(X0,X1)) | sK4(X0,X1) = sK4(X2,X3)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f100,f36])).
% 0.19/0.52  fof(f100,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (sK0 != k1_relat_1(sK4(X0,X1)) | sK0 != X2 | ~v1_relat_1(sK4(X0,X1)) | sK4(X0,X1) = sK4(X2,X3)) )),
% 0.19/0.52    inference(resolution,[],[f97,f37])).
% 0.19/0.52  fof(f97,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK0 != X1 | ~v1_relat_1(X0) | sK4(X1,X2) = X0) )),
% 0.19/0.52    inference(forward_demodulation,[],[f96,f38])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK4(X1,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X1,X2) = X0) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f94,f36])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK4(X1,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X1,X2) = X0 | ~v1_relat_1(sK4(X1,X2))) )),
% 0.19/0.52    inference(resolution,[],[f24,f37])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (5851)------------------------------
% 0.19/0.52  % (5851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (5851)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (5851)Memory used [KB]: 6524
% 0.19/0.52  % (5851)Time elapsed: 0.111 s
% 0.19/0.52  % (5851)------------------------------
% 0.19/0.52  % (5851)------------------------------
% 0.19/0.52  % (5850)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.52  % (5821)Success in time 0.169 s
%------------------------------------------------------------------------------
