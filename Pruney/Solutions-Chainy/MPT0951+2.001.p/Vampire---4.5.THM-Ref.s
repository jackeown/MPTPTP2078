%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 148 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   32
%              Number of atoms          :  371 (1015 expanded)
%              Number of equality atoms :   39 ( 239 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f29])).

fof(f29,plain,(
    r2_wellord2(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_wellord2(sK0,sK2)
    & r2_wellord2(sK1,sK2)
    & r2_wellord2(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_wellord2(X0,X2)
        & r2_wellord2(X1,X2)
        & r2_wellord2(X0,X1) )
   => ( ~ r2_wellord2(sK0,sK2)
      & r2_wellord2(sK1,sK2)
      & r2_wellord2(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_wellord2(X0,X2)
      & r2_wellord2(X1,X2)
      & r2_wellord2(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_wellord2(X0,X2)
      & r2_wellord2(X1,X2)
      & r2_wellord2(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_wellord2(X1,X2)
          & r2_wellord2(X0,X1) )
       => r2_wellord2(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_wellord2(X1,X2)
        & r2_wellord2(X0,X1) )
     => r2_wellord2(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord2)).

fof(f157,plain,(
    ~ r2_wellord2(sK1,sK2) ),
    inference(resolution,[],[f147,f28])).

fof(f28,plain,(
    r2_wellord2(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_wellord2(sK0,X0)
      | ~ r2_wellord2(X0,sK2) ) ),
    inference(resolution,[],[f146,f30])).

fof(f30,plain,(
    ~ r2_wellord2(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X2,X1)
      | ~ r2_wellord2(X2,X0)
      | ~ r2_wellord2(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_wellord2(X2,X0)
      | r2_wellord2(X2,X1)
      | ~ r2_wellord2(X0,X1)
      | ~ r2_wellord2(X0,X1) ) ),
    inference(superposition,[],[f143,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK3(X0,X1)) = X0
      | ~ r2_wellord2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_wellord2(X0,X1)
        | ! [X2] :
            ( k2_relat_1(X2) != X1
            | k1_relat_1(X2) != X0
            | ~ v2_funct_1(X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ( k2_relat_1(sK3(X0,X1)) = X1
          & k1_relat_1(sK3(X0,X1)) = X0
          & v2_funct_1(sK3(X0,X1))
          & v1_funct_1(sK3(X0,X1))
          & v1_relat_1(sK3(X0,X1)) )
        | ~ r2_wellord2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k2_relat_1(X3) = X1
          & k1_relat_1(X3) = X0
          & v2_funct_1(X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( k2_relat_1(sK3(X0,X1)) = X1
        & k1_relat_1(sK3(X0,X1)) = X0
        & v2_funct_1(sK3(X0,X1))
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_wellord2(X0,X1)
        | ! [X2] :
            ( k2_relat_1(X2) != X1
            | k1_relat_1(X2) != X0
            | ~ v2_funct_1(X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ? [X3] :
            ( k2_relat_1(X3) = X1
            & k1_relat_1(X3) = X0
            & v2_funct_1(X3)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        | ~ r2_wellord2(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_wellord2(X0,X1)
        | ! [X2] :
            ( k2_relat_1(X2) != X1
            | k1_relat_1(X2) != X0
            | ~ v2_funct_1(X2)
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) ) )
      & ( ? [X2] :
            ( k2_relat_1(X2) = X1
            & k1_relat_1(X2) = X0
            & v2_funct_1(X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        | ~ r2_wellord2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_wellord2(X0,X1)
    <=> ? [X2] :
          ( k2_relat_1(X2) = X1
          & k1_relat_1(X2) = X0
          & v2_funct_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord2)).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_wellord2(X2,k1_relat_1(sK3(X0,X1)))
      | r2_wellord2(X2,X1)
      | ~ r2_wellord2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f142,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK3(X0,X1))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X2,X1)
      | ~ r2_wellord2(X2,k1_relat_1(sK3(X0,X1)))
      | ~ v1_funct_1(sK3(X0,X1))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_funct_1(sK3(X0,X1))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X2,X1)
      | ~ r2_wellord2(X2,k1_relat_1(sK3(X0,X1)))
      | ~ v2_funct_1(sK3(X0,X1))
      | ~ v1_funct_1(sK3(X0,X1))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f139,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK3(X0,X1))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X2,X1)
      | ~ v1_relat_1(sK3(X0,X1))
      | ~ r2_wellord2(X2,k1_relat_1(sK3(X0,X1)))
      | ~ v2_funct_1(sK3(X0,X1))
      | ~ v1_funct_1(sK3(X0,X1))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(superposition,[],[f135,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK3(X0,X1)) = X1
      | ~ r2_wellord2(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_wellord2(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_wellord2(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_wellord2(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ r2_wellord2(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r2_wellord2(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ r2_wellord2(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f127,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f126,f41])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK3(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK3(X0,X2))
      | ~ v1_relat_1(sK3(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(sK3(X0,X2))
      | ~ v1_funct_1(sK3(X0,X2))
      | ~ v1_relat_1(sK3(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

% (25071)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X2),X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(sK3(X0,X2))
      | ~ v1_funct_1(sK3(X0,X2))
      | ~ v1_relat_1(sK3(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_funct_1(k5_relat_1(sK3(X0,X2),X1))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X2),X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(sK3(X0,X2))
      | ~ v1_funct_1(sK3(X0,X2))
      | ~ v1_relat_1(sK3(X0,X2)) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X1,X2))
      | ~ v1_funct_1(k5_relat_1(sK3(X0,X2),X1))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X2),X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r2_wellord2(X0,X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(sK3(X0,X2))
      | ~ v1_funct_1(sK3(X0,X2))
      | ~ v1_relat_1(sK3(X0,X2)) ) ),
    inference(resolution,[],[f118,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | r2_wellord2(X0,k9_relat_1(X2,X1))
      | ~ v1_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,k1_relat_1(X2))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,k9_relat_1(X2,X1))
      | ~ v2_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,k1_relat_1(X2))
      | ~ r2_wellord2(X0,X1)
      | ~ r2_wellord2(X0,X1) ) ),
    inference(superposition,[],[f90,f44])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(k1_relat_1(sK3(X0,X1)),k9_relat_1(X2,X1))
      | ~ v2_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,k1_relat_1(X2))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(k1_relat_1(sK3(X0,X1)),k9_relat_1(X2,X1))
      | ~ v2_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_funct_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(k5_relat_1(sK3(X0,X1),X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK3(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X2))
      | ~ r2_wellord2(X0,X1) ) ),
    inference(superposition,[],[f76,f45])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_wellord2(k1_relat_1(X0),k9_relat_1(X1,k2_relat_1(X0)))
      | ~ v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_wellord2(k1_relat_1(X0),k9_relat_1(X1,k2_relat_1(X0)))
      | ~ v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f66,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_wellord2(k1_relat_1(k5_relat_1(X0,X1)),k9_relat_1(X1,k2_relat_1(X0)))
      | ~ v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f50,plain,(
    ! [X2] :
      ( r2_wellord2(k1_relat_1(X2),k2_relat_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_wellord2(X0,k2_relat_1(X2))
      | k1_relat_1(X2) != X0
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_wellord2(X0,X1)
      | k2_relat_1(X2) != X1
      | k1_relat_1(X2) != X0
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (25055)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (25053)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (25063)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (25055)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f157,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    r2_wellord2(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ~r2_wellord2(sK0,sK2) & r2_wellord2(sK1,sK2) & r2_wellord2(sK0,sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r2_wellord2(X0,X2) & r2_wellord2(X1,X2) & r2_wellord2(X0,X1)) => (~r2_wellord2(sK0,sK2) & r2_wellord2(sK1,sK2) & r2_wellord2(sK0,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r2_wellord2(X0,X2) & r2_wellord2(X1,X2) & r2_wellord2(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r2_wellord2(X0,X2) & (r2_wellord2(X1,X2) & r2_wellord2(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((r2_wellord2(X1,X2) & r2_wellord2(X0,X1)) => r2_wellord2(X0,X2))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_wellord2(X1,X2) & r2_wellord2(X0,X1)) => r2_wellord2(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord2)).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ~r2_wellord2(sK1,sK2)),
% 0.20/0.48    inference(resolution,[],[f147,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    r2_wellord2(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_wellord2(sK0,X0) | ~r2_wellord2(X0,sK2)) )),
% 0.20/0.48    inference(resolution,[],[f146,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~r2_wellord2(sK0,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_wellord2(X2,X1) | ~r2_wellord2(X2,X0) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f145])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_wellord2(X2,X0) | r2_wellord2(X2,X1) | ~r2_wellord2(X0,X1) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.48    inference(superposition,[],[f143,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0 | ~r2_wellord2(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_wellord2(X0,X1) | ! [X2] : (k2_relat_1(X2) != X1 | k1_relat_1(X2) != X0 | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & ((k2_relat_1(sK3(X0,X1)) = X1 & k1_relat_1(sK3(X0,X1)) = X0 & v2_funct_1(sK3(X0,X1)) & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))) | ~r2_wellord2(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (k2_relat_1(X3) = X1 & k1_relat_1(X3) = X0 & v2_funct_1(X3) & v1_funct_1(X3) & v1_relat_1(X3)) => (k2_relat_1(sK3(X0,X1)) = X1 & k1_relat_1(sK3(X0,X1)) = X0 & v2_funct_1(sK3(X0,X1)) & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_wellord2(X0,X1) | ! [X2] : (k2_relat_1(X2) != X1 | k1_relat_1(X2) != X0 | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X3] : (k2_relat_1(X3) = X1 & k1_relat_1(X3) = X0 & v2_funct_1(X3) & v1_funct_1(X3) & v1_relat_1(X3)) | ~r2_wellord2(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_wellord2(X0,X1) | ! [X2] : (k2_relat_1(X2) != X1 | k1_relat_1(X2) != X0 | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X2] : (k2_relat_1(X2) = X1 & k1_relat_1(X2) = X0 & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) | ~r2_wellord2(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_wellord2(X0,X1) <=> ? [X2] : (k2_relat_1(X2) = X1 & k1_relat_1(X2) = X0 & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord2)).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_wellord2(X2,k1_relat_1(sK3(X0,X1))) | r2_wellord2(X2,X1) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f142,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X2,X1) | ~r2_wellord2(X2,k1_relat_1(sK3(X0,X1))) | ~v1_funct_1(sK3(X0,X1)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_funct_1(sK3(X0,X1)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X2,X1) | ~r2_wellord2(X2,k1_relat_1(sK3(X0,X1))) | ~v2_funct_1(sK3(X0,X1)) | ~v1_funct_1(sK3(X0,X1)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f139,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X2,X1) | ~v1_relat_1(sK3(X0,X1)) | ~r2_wellord2(X2,k1_relat_1(sK3(X0,X1))) | ~v2_funct_1(sK3(X0,X1)) | ~v1_funct_1(sK3(X0,X1)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(superposition,[],[f135,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(sK3(X0,X1)) = X1 | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_wellord2(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_wellord2(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_wellord2(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~r2_wellord2(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f128])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_wellord2(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~r2_wellord2(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(superposition,[],[f127,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f126,f41])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK3(X0,X2))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f125,f42])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_funct_1(sK3(X0,X2)) | ~v1_relat_1(sK3(X0,X2))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f43])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(sK3(X0,X2)) | ~v1_funct_1(sK3(X0,X2)) | ~v1_relat_1(sK3(X0,X2))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f123,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.20/0.49  % (25071)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_relat_1(k5_relat_1(sK3(X0,X2),X1)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(sK3(X0,X2)) | ~v1_funct_1(sK3(X0,X2)) | ~v1_relat_1(sK3(X0,X2))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f122,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_funct_1(k5_relat_1(sK3(X0,X2),X1)) | ~v1_relat_1(k5_relat_1(sK3(X0,X2),X1)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(sK3(X0,X2)) | ~v1_funct_1(sK3(X0,X2)) | ~v1_relat_1(sK3(X0,X2))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X1,X2)) | ~v1_funct_1(k5_relat_1(sK3(X0,X2),X1)) | ~v1_relat_1(k5_relat_1(sK3(X0,X2),X1)) | ~v1_relat_1(X1) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r2_wellord2(X0,X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(sK3(X0,X2)) | ~v1_funct_1(sK3(X0,X2)) | ~v1_relat_1(sK3(X0,X2))) )),
% 0.20/0.49    inference(resolution,[],[f118,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_funct_1(k5_relat_1(sK3(X0,X1),X2)) | r2_wellord2(X0,k9_relat_1(X2,X1)) | ~v1_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(X2) | ~r1_tarski(X1,k1_relat_1(X2)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,k9_relat_1(X2,X1)) | ~v2_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(X2) | ~r1_tarski(X1,k1_relat_1(X2)) | ~r2_wellord2(X0,X1) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(superposition,[],[f90,f44])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(k1_relat_1(sK3(X0,X1)),k9_relat_1(X2,X1)) | ~v2_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(X2) | ~r1_tarski(X1,k1_relat_1(X2)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f86,f41])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(k1_relat_1(sK3(X0,X1)),k9_relat_1(X2,X1)) | ~v2_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_funct_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(k5_relat_1(sK3(X0,X1),X2)) | ~v1_relat_1(X2) | ~v1_relat_1(sK3(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X2)) | ~r2_wellord2(X0,X1)) )),
% 0.20/0.49    inference(superposition,[],[f76,f45])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_wellord2(k1_relat_1(X0),k9_relat_1(X1,k2_relat_1(X0))) | ~v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_wellord2(k1_relat_1(X0),k9_relat_1(X1,k2_relat_1(X0))) | ~v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(superposition,[],[f66,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_wellord2(k1_relat_1(k5_relat_1(X0,X1)),k9_relat_1(X1,k2_relat_1(X0))) | ~v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(superposition,[],[f50,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2] : (r2_wellord2(k1_relat_1(X2),k2_relat_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(equality_resolution,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0] : (r2_wellord2(X0,k2_relat_1(X2)) | k1_relat_1(X2) != X0 | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(equality_resolution,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_wellord2(X0,X1) | k2_relat_1(X2) != X1 | k1_relat_1(X2) != X0 | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (25055)------------------------------
% 0.20/0.49  % (25055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25055)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (25055)Memory used [KB]: 6140
% 0.20/0.49  % (25055)Time elapsed: 0.096 s
% 0.20/0.49  % (25055)------------------------------
% 0.20/0.49  % (25055)------------------------------
% 0.20/0.49  % (25050)Success in time 0.14 s
%------------------------------------------------------------------------------
