%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 (1031 expanded)
%              Number of leaves         :   12 ( 386 expanded)
%              Depth                    :   30
%              Number of atoms          :  417 (10588 expanded)
%              Number of equality atoms :  137 (4992 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(subsumption_resolution,[],[f430,f36])).

fof(f36,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK2 != sK3
    & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
    & sK0 = k1_relat_1(sK3)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k2_relat_1(sK1)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                & k1_relat_1(X3) = X0
                & k1_relat_1(X2) = X0
                & k2_relat_1(X1) = X0
                & v1_funct_1(X3)
                & v1_relat_1(X3) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
              & k1_relat_1(X3) = sK0
              & k1_relat_1(X2) = sK0
              & sK0 = k2_relat_1(sK1)
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( X2 != X3
            & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
            & k1_relat_1(X3) = sK0
            & k1_relat_1(X2) = sK0
            & sK0 = k2_relat_1(sK1)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK2 != X3
          & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2)
          & k1_relat_1(X3) = sK0
          & sK0 = k1_relat_1(sK2)
          & sK0 = k2_relat_1(sK1)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( sK2 != X3
        & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2)
        & k1_relat_1(X3) = sK0
        & sK0 = k1_relat_1(sK2)
        & sK0 = k2_relat_1(sK1)
        & v1_funct_1(X3)
        & v1_relat_1(X3) )
   => ( sK2 != sK3
      & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
      & sK0 = k1_relat_1(sK3)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k2_relat_1(sK1)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

fof(f430,plain,(
    sK0 != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f429,f37])).

fof(f37,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f429,plain,(
    k1_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f428,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f428,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f427,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f427,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f426,f33])).

fof(f33,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f426,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f425,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f425,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f424,f39])).

fof(f39,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f424,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f421])).

fof(f421,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f41,f400])).

fof(f400,plain,(
    k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(sK2,sK4(sK2,sK3)) ),
    inference(forward_demodulation,[],[f399,f383])).

fof(f383,plain,(
    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3))) ),
    inference(forward_demodulation,[],[f376,f214])).

fof(f214,plain,(
    sK4(sK2,sK3) = k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3))) ),
    inference(resolution,[],[f208,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f97,f35])).

fof(f35,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK7(sK1,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK7(sK1,X0)) = X0
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X1)) = X1
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f48,f51])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

% (19204)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (19213)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (19210)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (19212)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f208,plain,(
    r2_hidden(sK4(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f207,f33])).

fof(f207,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f206,f37])).

fof(f206,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f204,f39])).

fof(f204,plain,
    ( sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f199,f34])).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sK2 = X0
      | k1_relat_1(X0) != sK0
      | r2_hidden(sK4(sK2,X0),sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f198,f31])).

fof(f198,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | sK2 = X0
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f194,f32])).

fof(f194,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK0)
      | sK2 = X0
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f376,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3))) = k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3)))) ),
    inference(resolution,[],[f350,f223])).

fof(f223,plain,(
    r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f222,f29])).

fof(f222,plain,
    ( r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f220,f30])).

fof(f220,plain,
    ( r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f218,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f218,plain,(
    r2_hidden(k4_tarski(sK7(sK1,sK4(sK2,sK3)),sK4(sK2,sK3)),sK1) ),
    inference(subsumption_resolution,[],[f217,f208])).

fof(f217,plain,
    ( r2_hidden(k4_tarski(sK7(sK1,sK4(sK2,sK3)),sK4(sK2,sK3)),sK1)
    | ~ r2_hidden(sK4(sK2,sK3),sK0) ),
    inference(superposition,[],[f86,f214])).

fof(f86,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(forward_demodulation,[],[f85,f35])).

fof(f85,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f84,f29])).

fof(f84,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f83,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f65,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f47,f51])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f52,f30])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f350,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f347,f31])).

fof(f347,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1)) ) ),
    inference(resolution,[],[f267,f32])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(sK1,X1),X0) = k1_funct_1(X1,k1_funct_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f264,f29])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(sK1,X1),X0) = k1_funct_1(X1,k1_funct_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f399,plain,(
    k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3))) ),
    inference(forward_demodulation,[],[f392,f214])).

fof(f392,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3))) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3)))) ),
    inference(resolution,[],[f352,f223])).

fof(f352,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | k1_funct_1(sK3,k1_funct_1(sK1,X2)) = k1_funct_1(k5_relat_1(sK1,sK2),X2) ) ),
    inference(forward_demodulation,[],[f351,f38])).

fof(f38,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f351,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK3),X2) = k1_funct_1(sK3,k1_funct_1(sK1,X2)) ) ),
    inference(subsumption_resolution,[],[f348,f33])).

fof(f348,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_relat_1(sK3)
      | k1_funct_1(k5_relat_1(sK1,sK3),X2) = k1_funct_1(sK3,k1_funct_1(sK1,X2)) ) ),
    inference(resolution,[],[f267,f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (19193)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (19203)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (19208)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (19191)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (19201)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (19199)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (19200)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (19211)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (19194)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (19207)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (19192)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (19196)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.55  % (19195)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.55  % (19202)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.56  % (19214)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  % (19216)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.56  % (19206)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.56  % (19215)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.57  % (19198)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.57  % (19197)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.57  % (19205)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.57  % (19209)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.57  % (19194)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f431,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f430,f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ((sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f17,f16,f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) => (sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f8,plain,(
% 0.20/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f7])).
% 0.20/0.57  fof(f7,plain,(
% 0.20/0.57    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 0.20/0.57    inference(negated_conjecture,[],[f5])).
% 0.20/0.57  fof(f5,conjecture,(
% 0.20/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).
% 0.20/0.57  fof(f430,plain,(
% 0.20/0.57    sK0 != k1_relat_1(sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f429,f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f429,plain,(
% 0.20/0.57    k1_relat_1(sK2) != k1_relat_1(sK3)),
% 0.20/0.57    inference(subsumption_resolution,[],[f428,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    v1_relat_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f428,plain,(
% 0.20/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f427,f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    v1_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f427,plain,(
% 0.20/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f426,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    v1_relat_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f426,plain,(
% 0.20/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f425,f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f425,plain,(
% 0.20/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f424,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    sK2 != sK3),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f424,plain,(
% 0.20/0.57    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f421])).
% 0.20/0.57  fof(f421,plain,(
% 0.20/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(superposition,[],[f41,f400])).
% 0.20/0.57  fof(f400,plain,(
% 0.20/0.57    k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(sK2,sK4(sK2,sK3))),
% 0.20/0.57    inference(forward_demodulation,[],[f399,f383])).
% 0.20/0.57  fof(f383,plain,(
% 0.20/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3)))),
% 0.20/0.57    inference(forward_demodulation,[],[f376,f214])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    sK4(sK2,sK3) = k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3)))),
% 0.20/0.57    inference(resolution,[],[f208,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK7(sK1,X0)) = X0) )),
% 0.20/0.57    inference(forward_demodulation,[],[f97,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    sK0 = k2_relat_1(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK1,sK7(sK1,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f94,f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    v1_relat_1(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK1,sK7(sK1,X0)) = X0 | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.20/0.57    inference(resolution,[],[f55,f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    v1_funct_1(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,sK7(X0,X1)) = X1 | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 0.20/0.57    inference(resolution,[],[f48,f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.57    inference(equality_resolution,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  % (19204)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.58  % (19213)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.59  % (19210)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.59  % (19212)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.59    inference(rectify,[],[f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.59    inference(nnf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.59    inference(flattening,[],[f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.59    inference(nnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.59    inference(flattening,[],[f13])).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.59  fof(f208,plain,(
% 0.20/0.59    r2_hidden(sK4(sK2,sK3),sK0)),
% 0.20/0.59    inference(subsumption_resolution,[],[f207,f33])).
% 0.20/0.59  fof(f207,plain,(
% 0.20/0.59    r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3)),
% 0.20/0.59    inference(subsumption_resolution,[],[f206,f37])).
% 0.20/0.59  fof(f206,plain,(
% 0.20/0.59    sK0 != k1_relat_1(sK3) | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3)),
% 0.20/0.59    inference(subsumption_resolution,[],[f204,f39])).
% 0.20/0.59  fof(f204,plain,(
% 0.20/0.59    sK2 = sK3 | sK0 != k1_relat_1(sK3) | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3)),
% 0.20/0.59    inference(resolution,[],[f199,f34])).
% 0.20/0.59  fof(f199,plain,(
% 0.20/0.59    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | k1_relat_1(X0) != sK0 | r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f198,f31])).
% 0.20/0.59  fof(f198,plain,(
% 0.20/0.59    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f194,f32])).
% 0.20/0.59  fof(f194,plain,(
% 0.20/0.59    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.59    inference(superposition,[],[f40,f36])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f10,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.59    inference(flattening,[],[f9])).
% 0.20/0.59  fof(f9,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.59  fof(f376,plain,(
% 0.20/0.59    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3))) = k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3))))),
% 0.20/0.59    inference(resolution,[],[f350,f223])).
% 0.20/0.59  fof(f223,plain,(
% 0.20/0.59    r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1))),
% 0.20/0.59    inference(subsumption_resolution,[],[f222,f29])).
% 0.20/0.59  fof(f222,plain,(
% 0.20/0.59    r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.59    inference(subsumption_resolution,[],[f220,f30])).
% 0.20/0.59  fof(f220,plain,(
% 0.20/0.59    r2_hidden(sK7(sK1,sK4(sK2,sK3)),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.59    inference(resolution,[],[f218,f47])).
% 0.20/0.59  fof(f47,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f218,plain,(
% 0.20/0.59    r2_hidden(k4_tarski(sK7(sK1,sK4(sK2,sK3)),sK4(sK2,sK3)),sK1)),
% 0.20/0.59    inference(subsumption_resolution,[],[f217,f208])).
% 0.20/0.59  fof(f217,plain,(
% 0.20/0.59    r2_hidden(k4_tarski(sK7(sK1,sK4(sK2,sK3)),sK4(sK2,sK3)),sK1) | ~r2_hidden(sK4(sK2,sK3),sK0)),
% 0.20/0.59    inference(superposition,[],[f86,f214])).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X1] : (r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f85,f35])).
% 0.20/0.59  fof(f85,plain,(
% 0.20/0.59    ( ! [X1] : (r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f84,f29])).
% 0.20/0.59  fof(f84,plain,(
% 0.20/0.59    ( ! [X1] : (r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f83,f30])).
% 0.20/0.59  fof(f83,plain,(
% 0.20/0.59    ( ! [X1] : (r2_hidden(k4_tarski(sK7(sK1,X1),k1_funct_1(sK1,sK7(sK1,X1))),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.20/0.59    inference(resolution,[],[f65,f54])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 0.20/0.59    inference(resolution,[],[f47,f51])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f62,f29])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.59    inference(resolution,[],[f52,f30])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.59    inference(equality_resolution,[],[f49])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f350,plain,(
% 0.20/0.59    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f347,f31])).
% 0.20/0.59  fof(f347,plain,(
% 0.20/0.59    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(k5_relat_1(sK1,sK2),X1) = k1_funct_1(sK2,k1_funct_1(sK1,X1))) )),
% 0.20/0.59    inference(resolution,[],[f267,f32])).
% 0.20/0.59  fof(f267,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK1,X1),X0) = k1_funct_1(X1,k1_funct_1(sK1,X0))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f264,f29])).
% 0.20/0.59  fof(f264,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(sK1,X1),X0) = k1_funct_1(X1,k1_funct_1(sK1,X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.59    inference(resolution,[],[f42,f30])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.59    inference(flattening,[],[f11])).
% 0.20/0.59  fof(f11,plain,(
% 0.20/0.59    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.59  fof(f399,plain,(
% 0.20/0.59    k1_funct_1(sK3,sK4(sK2,sK3)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3)))),
% 0.20/0.59    inference(forward_demodulation,[],[f392,f214])).
% 0.20/0.59  fof(f392,plain,(
% 0.20/0.59    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK2,sK3))) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK2,sK3))))),
% 0.20/0.59    inference(resolution,[],[f352,f223])).
% 0.20/0.59  fof(f352,plain,(
% 0.20/0.59    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | k1_funct_1(sK3,k1_funct_1(sK1,X2)) = k1_funct_1(k5_relat_1(sK1,sK2),X2)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f351,f38])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f351,plain,(
% 0.20/0.59    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK3),X2) = k1_funct_1(sK3,k1_funct_1(sK1,X2))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f348,f33])).
% 0.20/0.59  fof(f348,plain,(
% 0.20/0.59    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_relat_1(sK3) | k1_funct_1(k5_relat_1(sK1,sK3),X2) = k1_funct_1(sK3,k1_funct_1(sK1,X2))) )),
% 0.20/0.59    inference(resolution,[],[f267,f34])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (19194)------------------------------
% 0.20/0.59  % (19194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (19194)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (19194)Memory used [KB]: 6908
% 0.20/0.59  % (19194)Time elapsed: 0.149 s
% 0.20/0.59  % (19194)------------------------------
% 0.20/0.59  % (19194)------------------------------
% 0.20/0.59  % (19190)Success in time 0.239 s
%------------------------------------------------------------------------------
