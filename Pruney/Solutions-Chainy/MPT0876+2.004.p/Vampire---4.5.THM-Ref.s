%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 366 expanded)
%              Number of leaves         :    4 (  85 expanded)
%              Depth                    :   56
%              Number of atoms          :  349 (1485 expanded)
%              Number of equality atoms :  348 (1484 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f460,plain,(
    $false ),
    inference(subsumption_resolution,[],[f459,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f459,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f452,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f452,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f14,f446])).

fof(f446,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f443,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f443,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f442])).

fof(f442,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f14,f434])).

fof(f434,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f433,f22])).

fof(f22,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f433,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) ),
    inference(forward_demodulation,[],[f419,f22])).

% (4013)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f419,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5) ),
    inference(backward_demodulation,[],[f20,f417])).

fof(f417,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f416,f11])).

fof(f416,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f408,f12])).

fof(f408,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f407])).

fof(f407,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f14,f392])).

fof(f392,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f384,f13])).

fof(f384,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f14,f363])).

fof(f363,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f362,f22])).

fof(f362,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f354,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f354,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f20,f353])).

fof(f353,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f352,f11])).

fof(f352,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f345,f12])).

fof(f345,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f344])).

fof(f344,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f14,f330])).

fof(f330,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f323,f13])).

fof(f323,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f14,f309])).

fof(f309,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f306,f21])).

fof(f306,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f20,f301])).

fof(f301,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f300,f14])).

fof(f300,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f298,f22])).

fof(f298,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f25,f279])).

fof(f279,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(global_subsumption,[],[f60,f268,f278])).

% (4012)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f278,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f277,f11])).

fof(f277,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f274,f12])).

fof(f274,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f75,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f75,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f70,f14])).

fof(f70,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f17,f65])).

fof(f65,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f62,f13])).

fof(f62,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f28,f17])).

fof(f28,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f17,f20])).

fof(f268,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(subsumption_resolution,[],[f262,f13])).

fof(f262,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(superposition,[],[f14,f249])).

fof(f249,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(forward_demodulation,[],[f246,f21])).

fof(f246,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(superposition,[],[f20,f241])).

fof(f241,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(subsumption_resolution,[],[f240,f14])).

fof(f240,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(subsumption_resolution,[],[f238,f22])).

fof(f238,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | sK1 = sK4 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | sK1 = sK4 ),
    inference(superposition,[],[f25,f222])).

fof(f222,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | sK1 = sK4 ),
    inference(subsumption_resolution,[],[f221,f11])).

fof(f221,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f218,f12])).

fof(f218,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f74,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f69,f14])).

fof(f69,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f18,f65])).

fof(f60,plain,
    ( sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK5 ),
    inference(subsumption_resolution,[],[f59,f11])).

fof(f59,plain,
    ( sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK5 ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,
    ( sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(subsumption_resolution,[],[f57,f12])).

fof(f57,plain,
    ( sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK1 ),
    inference(inner_rewriting,[],[f56])).

fof(f56,plain,
    ( sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( sK2 != sK2
    | sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f9,f52])).

fof(f52,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f51,f14])).

fof(f51,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK3
    | sK2 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f47,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK3
    | sK2 = sK5
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | sK2 = sK5
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f25,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | sK2 = sK5
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | sK2 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f14,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK5
    | sK2 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f32,f13])).

fof(f32,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f31,f18])).

fof(f31,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f18,f20])).

fof(f9,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f10,f19,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f10,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (4015)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (4015)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (4023)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (4031)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f460,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f459,f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.22/0.52    inference(flattening,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f4])).
% 0.22/0.52  fof(f4,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.22/0.52  fof(f459,plain,(
% 0.22/0.52    k1_xboole_0 = sK0),
% 0.22/0.52    inference(subsumption_resolution,[],[f452,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f452,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f451])).
% 0.22/0.52  fof(f451,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.52    inference(superposition,[],[f14,f446])).
% 0.22/0.52  fof(f446,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f443,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    k1_xboole_0 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f443,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f442])).
% 0.22/0.52  fof(f442,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.52    inference(superposition,[],[f14,f434])).
% 0.22/0.52  fof(f434,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f433,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f433,plain,(
% 0.22/0.52    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)),
% 0.22/0.52    inference(forward_demodulation,[],[f419,f22])).
% 0.22/0.53  % (4013)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5)),
% 0.22/0.53    inference(backward_demodulation,[],[f20,f417])).
% 0.22/0.53  fof(f417,plain,(
% 0.22/0.53    k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f416,f11])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f408,f12])).
% 0.22/0.53  fof(f408,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f407])).
% 0.22/0.53  fof(f407,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3),
% 0.22/0.53    inference(superposition,[],[f14,f392])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f384,f13])).
% 0.22/0.53  fof(f384,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f383])).
% 0.22/0.53  fof(f383,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(superposition,[],[f14,f363])).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(forward_demodulation,[],[f362,f22])).
% 0.22/0.53  fof(f362,plain,(
% 0.22/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(forward_demodulation,[],[f354,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f354,plain,(
% 0.22/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(superposition,[],[f20,f353])).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f352,f11])).
% 0.22/0.53  fof(f352,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f345,f12])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f344])).
% 0.22/0.53  fof(f344,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f14,f330])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f323,f13])).
% 0.22/0.53  fof(f323,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f322])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f14,f309])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(forward_demodulation,[],[f306,f21])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f20,f301])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f300,f14])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f298,f22])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f281])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f25,f279])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(global_subsumption,[],[f60,f268,f278])).
% 0.22/0.53  % (4012)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    sK0 = sK3 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f277,f11])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    sK0 = sK3 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK0),
% 0.22/0.53    inference(subsumption_resolution,[],[f274,f12])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    sK0 = sK3 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(superposition,[],[f75,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f70,f14])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f17,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f62,f13])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f28,f17])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(superposition,[],[f17,f20])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f262,f13])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f261])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(superposition,[],[f14,f249])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(forward_demodulation,[],[f246,f21])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(superposition,[],[f20,f241])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f240,f14])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f238,f22])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK1 = sK4),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f224])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | sK1 = sK4),
% 0.22/0.53    inference(superposition,[],[f25,f222])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | sK1 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f221,f11])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    sK1 = sK4 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK0),
% 0.22/0.53    inference(subsumption_resolution,[],[f218,f12])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    sK1 = sK4 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.53    inference(superposition,[],[f74,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f69,f14])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f18,f65])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK5),
% 0.22/0.53    inference(subsumption_resolution,[],[f59,f11])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK5),
% 0.22/0.53    inference(inner_rewriting,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5),
% 0.22/0.53    inference(subsumption_resolution,[],[f57,f12])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = sK1),
% 0.22/0.53    inference(inner_rewriting,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    sK2 != sK2 | sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f9,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    sK2 = sK5 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f51,f14])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK3 | sK2 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f47,f22])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK3 | sK2 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | sK2 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f25,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | sK2 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | sK2 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f14,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK5 | sK2 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f32,f13])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    sK2 = sK5 | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f31,f18])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(superposition,[],[f18,f20])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(superposition,[],[f14,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.22/0.53    inference(definition_unfolding,[],[f10,f19,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (4015)------------------------------
% 0.22/0.53  % (4015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4015)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (4015)Memory used [KB]: 6268
% 0.22/0.53  % (4015)Time elapsed: 0.101 s
% 0.22/0.53  % (4015)------------------------------
% 0.22/0.53  % (4015)------------------------------
% 0.22/0.53  % (4008)Success in time 0.169 s
%------------------------------------------------------------------------------
