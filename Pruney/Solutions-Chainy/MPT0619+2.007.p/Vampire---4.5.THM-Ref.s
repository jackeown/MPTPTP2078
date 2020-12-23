%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 278 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  238 ( 979 expanded)
%              Number of equality atoms :   89 ( 434 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f63,f205,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f205,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f86,f196])).

fof(f196,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(backward_demodulation,[],[f84,f195])).

fof(f195,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f194,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f194,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f182,f84])).

fof(f182,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k11_relat_1(sK1,sK0))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f123,f147])).

fof(f147,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,X0) = k1_tarski(k1_funct_1(sK1,X0))
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X6,X7] :
      ( k1_funct_1(sK1,X6) != X7
      | k1_xboole_0 = k11_relat_1(sK1,X6)
      | k11_relat_1(sK1,X6) = k1_tarski(X7) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X6,X7] :
      ( k1_funct_1(sK1,X6) != X7
      | k1_xboole_0 = k11_relat_1(sK1,X6)
      | k11_relat_1(sK1,X6) = k1_tarski(X7)
      | k11_relat_1(sK1,X6) = k1_tarski(X7)
      | k1_xboole_0 = k11_relat_1(sK1,X6) ) ),
    inference(superposition,[],[f52,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1,X0) = sK2(k11_relat_1(sK1,X0),X1)
      | k1_tarski(X1) = k11_relat_1(sK1,X0)
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f88,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f79,f36])).

% (23103)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0),X1)),sK1)
      | k1_xboole_0 = k11_relat_1(sK1,X0)
      | k1_tarski(X1) = k11_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
      | r2_hidden(k4_tarski(X1,X0),sK1) ) ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,(
    ~ r1_tarski(k2_relat_1(sK1),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f122,f39])).

fof(f39,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,
    ( k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0))
    | ~ r1_tarski(k2_relat_1(sK1),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(resolution,[],[f99,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

% (23105)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f99,plain,(
    r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f98,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f95,f84])).

fof(f95,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f90,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X1,k11_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(forward_demodulation,[],[f82,f38])).

fof(f38,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(subsumption_resolution,[],[f81,f36])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f62,f37])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f68,f66])).

fof(f66,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f65,f38])).

fof(f65,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f68,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0)) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f86,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f70,f66])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | r1_xboole_0(k1_tarski(sK0),X0) ) ),
    inference(forward_demodulation,[],[f69,f38])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

% (23119)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f63,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f49,f60])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (23110)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (23102)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (23100)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23110)Refutation not found, incomplete strategy% (23110)------------------------------
% 0.21/0.53  % (23110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23106)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (23116)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (23117)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (23101)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (23118)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (23109)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (23110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23110)Memory used [KB]: 10618
% 0.21/0.55  % (23110)Time elapsed: 0.110 s
% 0.21/0.55  % (23110)------------------------------
% 0.21/0.55  % (23110)------------------------------
% 0.21/0.55  % (23098)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (23101)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (23108)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (23108)Refutation not found, incomplete strategy% (23108)------------------------------
% 0.21/0.55  % (23108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23108)Memory used [KB]: 1791
% 0.21/0.55  % (23108)Time elapsed: 0.130 s
% 0.21/0.55  % (23108)------------------------------
% 0.21/0.55  % (23108)------------------------------
% 0.21/0.55  % (23097)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (23106)Refutation not found, incomplete strategy% (23106)------------------------------
% 0.21/0.56  % (23106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f211,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f63,f205,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f199])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.56    inference(backward_demodulation,[],[f86,f196])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.56    inference(backward_demodulation,[],[f84,f195])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f194,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.56    inference(forward_demodulation,[],[f182,f84])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK1),k11_relat_1(sK1,sK0)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.56    inference(superposition,[],[f123,f147])).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ( ! [X0] : (k11_relat_1(sK1,X0) = k1_tarski(k1_funct_1(sK1,X0)) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f131])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ( ! [X6,X7] : (k1_funct_1(sK1,X6) != X7 | k1_xboole_0 = k11_relat_1(sK1,X6) | k11_relat_1(sK1,X6) = k1_tarski(X7)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    ( ! [X6,X7] : (k1_funct_1(sK1,X6) != X7 | k1_xboole_0 = k11_relat_1(sK1,X6) | k11_relat_1(sK1,X6) = k1_tarski(X7) | k11_relat_1(sK1,X6) = k1_tarski(X7) | k1_xboole_0 = k11_relat_1(sK1,X6)) )),
% 0.21/0.56    inference(superposition,[],[f52,f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_funct_1(sK1,X0) = sK2(k11_relat_1(sK1,X0),X1) | k1_tarski(X1) = k11_relat_1(sK1,X0) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f88,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f79,f36])).
% 0.21/0.56  % (23103)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    v1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.56    inference(negated_conjecture,[],[f13])).
% 0.21/0.56  fof(f13,conjecture,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f58,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    v1_funct_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0),X1)),sK1) | k1_xboole_0 = k11_relat_1(sK1,X0) | k1_tarski(X1) = k11_relat_1(sK1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f75,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | r2_hidden(k4_tarski(X1,X0),sK1)) )),
% 0.21/0.56    inference(resolution,[],[f56,f36])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK1),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f122,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) | ~r1_tarski(k2_relat_1(sK1),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.21/0.56    inference(resolution,[],[f99,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  % (23105)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(sK1))),
% 0.21/0.56    inference(resolution,[],[f98,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f95,f84])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.21/0.56    inference(resolution,[],[f90,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,k11_relat_1(sK1,X0))) )),
% 0.21/0.56    inference(resolution,[],[f55,f36])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 0.21/0.56    inference(resolution,[],[f83,f63])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f82,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f81,f36])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f62,f37])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.21/0.56    inference(superposition,[],[f68,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.56    inference(forward_demodulation,[],[f65,f38])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.21/0.56    inference(resolution,[],[f41,f36])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.21/0.56    inference(resolution,[],[f42,f36])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK1) | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.56    inference(superposition,[],[f70,f66])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_tarski(sK0),X0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f69,f38])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.21/0.56    inference(resolution,[],[f44,f36])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  % (23119)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.56    inference(resolution,[],[f49,f60])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (23101)------------------------------
% 0.21/0.56  % (23101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23101)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (23101)Memory used [KB]: 1791
% 0.21/0.56  % (23101)Time elapsed: 0.122 s
% 0.21/0.56  % (23101)------------------------------
% 0.21/0.56  % (23101)------------------------------
% 0.21/0.56  % (23111)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (23093)Success in time 0.199 s
%------------------------------------------------------------------------------
