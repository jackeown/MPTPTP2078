%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 563 expanded)
%              Number of leaves         :   13 ( 171 expanded)
%              Depth                    :   16
%              Number of atoms          :  423 (3777 expanded)
%              Number of equality atoms :  108 (1522 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23603)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f272,plain,(
    $false ),
    inference(subsumption_resolution,[],[f271,f123])).

fof(f123,plain,(
    ~ r2_hidden(k4_tarski(sK6(k1_relat_1(sK1),sK1),sK6(k1_relat_1(sK1),sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f113,f98])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k6_relat_1(k1_relat_1(sK1))
    & sK0 = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & sK0 = k5_relat_1(sK0,X1)
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k6_relat_1(k1_relat_1(X1)) != X1
        & sK0 = k5_relat_1(sK0,X1)
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK1 != k6_relat_1(k1_relat_1(sK1))
      & sK0 = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f95,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    sK6(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK6(k1_relat_1(sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f40,f43,f65])).

fof(f65,plain,(
    ! [X1] :
      ( sK6(k1_relat_1(X1),X1) != k1_funct_1(X1,sK6(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1))
            & r2_hidden(sK6(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f43,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f271,plain,(
    r2_hidden(k4_tarski(sK6(k1_relat_1(sK1),sK1),sK6(k1_relat_1(sK1),sK1)),sK1) ),
    inference(forward_demodulation,[],[f256,f242])).

fof(f242,plain,(
    sK6(k1_relat_1(sK1),sK1) = sK5(sK0,sK1,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),sK6(k1_relat_1(sK1),sK1)) ),
    inference(forward_demodulation,[],[f236,f152])).

fof(f152,plain,(
    sK6(k1_relat_1(sK1),sK1) = k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0)) ),
    inference(unit_resulting_resolution,[],[f112,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK0,sK7(X0,k1_relat_1(sK0),sK0)) = X0 ) ),
    inference(superposition,[],[f124,f78])).

fof(f78,plain,(
    k1_relat_1(sK1) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f70,f41])).

fof(f41,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK0,X1))
      | k1_funct_1(sK0,sK7(X0,X1,sK0)) = X0 ) ),
    inference(resolution,[],[f75,f84])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f81,f37])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | k1_funct_1(sK0,X2) = X3
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f38,f60])).

fof(f38,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X8,X7] :
      ( r2_hidden(k4_tarski(sK7(X7,X8,sK0),X7),sK0)
      | ~ r2_hidden(X7,k9_relat_1(sK0,X8)) ) ),
    inference(resolution,[],[f37,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f112,plain,(
    r2_hidden(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f40,f43,f66])).

fof(f66,plain,(
    ! [X1] :
      ( r2_hidden(sK6(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f236,plain,(
    k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0)) = sK5(sK0,sK1,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0))) ),
    inference(unit_resulting_resolution,[],[f126,f207])).

fof(f207,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK0))
      | k1_funct_1(sK0,X6) = sK5(sK0,sK1,X6,k1_funct_1(sK0,X6)) ) ),
    inference(resolution,[],[f131,f84])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,k1_funct_1(sK0,X0))),sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f107,f85])).

fof(f85,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(X4,k1_funct_1(sK0,X4)),sK0)
      | ~ r2_hidden(X4,k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f82,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK0,X4)),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f38,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0) ) ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f64,f42])).

fof(f42,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f126,plain,(
    r2_hidden(sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f112,f115])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0,k1_relat_1(sK0),sK0),k1_relat_1(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f76,f78])).

fof(f76,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k9_relat_1(sK0,X10))
      | r2_hidden(sK7(X9,X10,sK0),X10) ) ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f256,plain,(
    r2_hidden(k4_tarski(sK5(sK0,sK1,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),sK6(k1_relat_1(sK1),sK1)),sK6(k1_relat_1(sK1),sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f158,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1) ) ),
    inference(subsumption_resolution,[],[f108,f39])).

fof(f108,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f63,f42])).

fof(f63,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (23606)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f158,plain,(
    r2_hidden(k4_tarski(sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),sK6(k1_relat_1(sK1),sK1)),sK0) ),
    inference(backward_demodulation,[],[f130,f152])).

fof(f130,plain,(
    r2_hidden(k4_tarski(sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f126,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23592)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (23591)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (23602)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (23601)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23599)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (23594)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (23600)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (23598)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (23595)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (23604)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (23589)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23600)Refutation not found, incomplete strategy% (23600)------------------------------
% 0.21/0.53  % (23600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23600)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23600)Memory used [KB]: 10746
% 0.21/0.53  % (23600)Time elapsed: 0.053 s
% 0.21/0.53  % (23600)------------------------------
% 0.21/0.53  % (23600)------------------------------
% 0.21/0.54  % (23590)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (23593)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (23608)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.55  % (23604)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (23597)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  % (23603)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.55  fof(f272,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f271,f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ~r2_hidden(k4_tarski(sK6(k1_relat_1(sK1),sK1),sK6(k1_relat_1(sK1),sK1)),sK1)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f113,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f95,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    (sK1 != k6_relat_1(k1_relat_1(sK1)) & sK0 = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & sK0 = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & sK0 = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK1 != k6_relat_1(k1_relat_1(sK1)) & sK0 = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3 | ~v1_relat_1(sK1)) )),
% 0.21/0.55    inference(resolution,[],[f40,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    v1_funct_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    sK6(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK6(k1_relat_1(sK1),sK1))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f39,f40,f43,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X1] : (sK6(k1_relat_1(X1),X1) != k1_funct_1(X1,sK6(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK6(X0,X1) != k1_funct_1(X1,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(rectify,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    sK1 != k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK6(k1_relat_1(sK1),sK1),sK6(k1_relat_1(sK1),sK1)),sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f256,f242])).
% 0.21/0.55  fof(f242,plain,(
% 0.21/0.55    sK6(k1_relat_1(sK1),sK1) = sK5(sK0,sK1,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),sK6(k1_relat_1(sK1),sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f236,f152])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    sK6(k1_relat_1(sK1),sK1) = k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f112,f146])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,sK7(X0,k1_relat_1(sK0),sK0)) = X0) )),
% 0.21/0.55    inference(superposition,[],[f124,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    k1_relat_1(sK1) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f70,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f37,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK0,X1)) | k1_funct_1(sK0,sK7(X0,X1,sK0)) = X0) )),
% 0.21/0.55    inference(resolution,[],[f75,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f81,f37])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3 | ~v1_relat_1(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f38,f60])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    v1_funct_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X8,X7] : (r2_hidden(k4_tarski(sK7(X7,X8,sK0),X7),sK0) | ~r2_hidden(X7,k9_relat_1(sK0,X8))) )),
% 0.21/0.55    inference(resolution,[],[f37,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(rectify,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    r2_hidden(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK1))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f39,f40,f43,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X1] : (r2_hidden(sK6(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0)) = sK5(sK0,sK1,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0)))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f126,f207])).
% 0.21/0.55  fof(f207,plain,(
% 0.21/0.55    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK0)) | k1_funct_1(sK0,X6) = sK5(sK0,sK1,X6,k1_funct_1(sK0,X6))) )),
% 0.21/0.55    inference(resolution,[],[f131,f84])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,k1_funct_1(sK0,X0))),sK0) | ~r2_hidden(X0,k1_relat_1(sK0))) )),
% 0.21/0.55    inference(resolution,[],[f107,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X4] : (r2_hidden(k4_tarski(X4,k1_funct_1(sK0,X4)),sK0) | ~r2_hidden(X4,k1_relat_1(sK0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f82,f37])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK0,X4)),sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f38,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(equality_resolution,[],[f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f106,f39])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0) | ~v1_relat_1(sK1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f105,f37])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0) | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0) | ~v1_relat_1(sK1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(X0,X1),sK0) | r2_hidden(k4_tarski(X0,sK5(sK0,sK1,X0,X1)),sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.55    inference(superposition,[],[f64,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X8,X7,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(rectify,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    r2_hidden(sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),k1_relat_1(sK0))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f112,f115])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(X0,k1_relat_1(sK0),sK0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.56    inference(superposition,[],[f76,f78])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X10,X9] : (~r2_hidden(X9,k9_relat_1(sK0,X10)) | r2_hidden(sK7(X9,X10,sK0),X10)) )),
% 0.21/0.56    inference(resolution,[],[f37,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    r2_hidden(k4_tarski(sK5(sK0,sK1,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),sK6(k1_relat_1(sK1),sK1)),sK6(k1_relat_1(sK1),sK1)),sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f158,f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f108,f39])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f104,f37])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(X2,X3),sK0) | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(X2,X3),sK0) | r2_hidden(k4_tarski(sK5(sK0,sK1,X2,X3),X3),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.56    inference(superposition,[],[f63,f42])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X8,X7,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  % (23606)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    r2_hidden(k4_tarski(sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),sK6(k1_relat_1(sK1),sK1)),sK0)),
% 0.21/0.56    inference(backward_demodulation,[],[f130,f152])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    r2_hidden(k4_tarski(sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0),k1_funct_1(sK0,sK7(sK6(k1_relat_1(sK1),sK1),k1_relat_1(sK0),sK0))),sK0)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f37,f38,f126,f69])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (23604)------------------------------
% 0.21/0.56  % (23604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23604)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (23604)Memory used [KB]: 6396
% 0.21/0.56  % (23604)Time elapsed: 0.080 s
% 0.21/0.56  % (23604)------------------------------
% 0.21/0.56  % (23604)------------------------------
% 0.21/0.56  % (23588)Success in time 0.197 s
%------------------------------------------------------------------------------
