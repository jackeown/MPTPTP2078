%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 169 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  234 ( 885 expanded)
%              Number of equality atoms :  113 ( 410 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f187])).

fof(f187,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f150,f150])).

fof(f150,plain,(
    ! [X3] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X3 ),
    inference(subsumption_resolution,[],[f143,f28])).

fof(f143,plain,(
    ! [X3] :
      ( k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X3
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f75,f135])).

fof(f135,plain,(
    ! [X0] : sK1(sK0) = sK5(sK0,X0) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X2
      | sK0 != X0
      | sK5(X0,X1) = sK1(X2) ) ),
    inference(superposition,[],[f82,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK5(X0,X1)) = X0
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK5(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f82,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK5(X2,X3))
      | sK0 != X4
      | sK5(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK5(X2,X3))
      | sK0 != X4
      | ~ v1_relat_1(sK5(X2,X3))
      | sK5(X2,X3) = sK1(X4) ) ),
    inference(resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | sK0 != X1
      | ~ v1_relat_1(X0)
      | sK1(X1) = X0 ) ),
    inference(forward_demodulation,[],[f68,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK1(X1) = X0 ) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK1(X1) = X0
      | ~ v1_relat_1(sK1(X1)) ) ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f75,plain,(
    ! [X6,X5] :
      ( k1_funct_1(sK5(X5,X6),sK2(k1_xboole_0,X5)) = X6
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK5(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X12] :
      ( r2_hidden(sK2(k1_xboole_0,X12),X12)
      | k1_xboole_0 = X12 ) ),
    inference(forward_demodulation,[],[f63,f29])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f63,plain,(
    ! [X12] :
      ( k1_relat_1(k1_xboole_0) = X12
      | r2_hidden(sK2(k1_xboole_0,X12),X12) ) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f35,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (21505)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (21513)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (21527)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (21517)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (21511)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (21515)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (21511)Refutation not found, incomplete strategy% (21511)------------------------------
% 0.20/0.49  % (21511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21509)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (21529)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.49  % (21525)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (21508)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (21523)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.49  % (21519)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (21511)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21511)Memory used [KB]: 10618
% 0.20/0.49  % (21511)Time elapsed: 0.089 s
% 0.20/0.49  % (21511)------------------------------
% 0.20/0.49  % (21511)------------------------------
% 0.20/0.50  % (21505)Refutation not found, incomplete strategy% (21505)------------------------------
% 0.20/0.50  % (21505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21505)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21505)Memory used [KB]: 10490
% 0.20/0.50  % (21505)Time elapsed: 0.095 s
% 0.20/0.50  % (21505)------------------------------
% 0.20/0.50  % (21505)------------------------------
% 0.20/0.50  % (21506)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (21526)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (21508)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 1.20/0.51  % (21506)Refutation not found, incomplete strategy% (21506)------------------------------
% 1.20/0.51  % (21506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (21506)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (21506)Memory used [KB]: 10618
% 1.20/0.51  % (21506)Time elapsed: 0.107 s
% 1.20/0.51  % (21506)------------------------------
% 1.20/0.51  % (21506)------------------------------
% 1.20/0.51  % (21507)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.20/0.51  % (21518)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.20/0.51  % (21514)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.20/0.51  % (21518)Refutation not found, incomplete strategy% (21518)------------------------------
% 1.20/0.51  % (21518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (21510)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f261,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f28,f187])).
% 1.20/0.52  fof(f187,plain,(
% 1.20/0.52    ( ! [X0,X1] : (X0 = X1) )),
% 1.20/0.52    inference(superposition,[],[f150,f150])).
% 1.20/0.52  fof(f150,plain,(
% 1.20/0.52    ( ! [X3] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X3) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f143,f28])).
% 1.20/0.52  fof(f143,plain,(
% 1.20/0.52    ( ! [X3] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X3 | k1_xboole_0 = sK0) )),
% 1.20/0.52    inference(superposition,[],[f75,f135])).
% 1.20/0.52  fof(f135,plain,(
% 1.20/0.52    ( ! [X0] : (sK1(sK0) = sK5(sK0,X0)) )),
% 1.20/0.52    inference(equality_resolution,[],[f134])).
% 1.20/0.52  fof(f134,plain,(
% 1.20/0.52    ( ! [X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(sK0)) )),
% 1.20/0.52    inference(equality_resolution,[],[f133])).
% 1.20/0.52  fof(f133,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (sK0 != X2 | sK0 != X0 | sK5(X0,X1) = sK1(X2)) )),
% 1.20/0.52    inference(superposition,[],[f82,f45])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ! [X0,X1] : (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f25])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.20/0.52    inference(ennf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.20/0.52  fof(f82,plain,(
% 1.20/0.52    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK5(X2,X3)) | sK0 != X4 | sK5(X2,X3) = sK1(X4)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f80,f43])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f80,plain,(
% 1.20/0.52    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK5(X2,X3)) | sK0 != X4 | ~v1_relat_1(sK5(X2,X3)) | sK5(X2,X3) = sK1(X4)) )),
% 1.20/0.52    inference(resolution,[],[f69,f44])).
% 1.20/0.52  fof(f44,plain,(
% 1.20/0.52    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f69,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK0 != X1 | ~v1_relat_1(X0) | sK1(X1) = X0) )),
% 1.20/0.52    inference(forward_demodulation,[],[f68,f33])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f11,plain,(
% 1.20/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 1.20/0.52  fof(f68,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK1(X1) = X0) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f66,f31])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f66,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK1(X1) = X0 | ~v1_relat_1(sK1(X1))) )),
% 1.20/0.52    inference(resolution,[],[f27,f32])).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f10,plain,(
% 1.20/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.20/0.52    inference(flattening,[],[f9])).
% 1.20/0.52  fof(f9,plain,(
% 1.20/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.20/0.52    inference(ennf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,negated_conjecture,(
% 1.20/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.20/0.52    inference(negated_conjecture,[],[f7])).
% 1.20/0.52  fof(f7,conjecture,(
% 1.20/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 1.20/0.52  fof(f75,plain,(
% 1.20/0.52    ( ! [X6,X5] : (k1_funct_1(sK5(X5,X6),sK2(k1_xboole_0,X5)) = X6 | k1_xboole_0 = X5) )),
% 1.20/0.52    inference(resolution,[],[f65,f46])).
% 1.20/0.52  fof(f46,plain,(
% 1.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK5(X0,X1),X3) = X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f65,plain,(
% 1.20/0.52    ( ! [X12] : (r2_hidden(sK2(k1_xboole_0,X12),X12) | k1_xboole_0 = X12) )),
% 1.20/0.52    inference(forward_demodulation,[],[f63,f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.20/0.52  fof(f63,plain,(
% 1.20/0.52    ( ! [X12] : (k1_relat_1(k1_xboole_0) = X12 | r2_hidden(sK2(k1_xboole_0,X12),X12)) )),
% 1.20/0.52    inference(resolution,[],[f38,f51])).
% 1.20/0.52  fof(f51,plain,(
% 1.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.20/0.52    inference(superposition,[],[f35,f49])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.20/0.52    inference(equality_resolution,[],[f42])).
% 1.20/0.52  fof(f42,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.20/0.52    inference(flattening,[],[f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.20/0.52    inference(nnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.20/0.52    inference(rectify,[],[f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.20/0.52    inference(nnf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    k1_xboole_0 != sK0),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (21508)------------------------------
% 1.20/0.52  % (21508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (21508)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (21508)Memory used [KB]: 6396
% 1.20/0.52  % (21508)Time elapsed: 0.094 s
% 1.20/0.52  % (21508)------------------------------
% 1.20/0.52  % (21508)------------------------------
% 1.20/0.52  % (21504)Success in time 0.164 s
%------------------------------------------------------------------------------
