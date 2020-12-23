%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:46 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 326 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   24
%              Number of atoms          :  238 (1109 expanded)
%              Number of equality atoms :  102 ( 513 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f51])).

fof(f51,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35])).

fof(f35,plain,
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

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f249,plain,(
    k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f248])).

fof(f248,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f245,f152])).

fof(f152,plain,(
    k1_xboole_0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f151,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f151,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f143,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f143,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 != k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f142,f50])).

fof(f50,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f142,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f141,f48])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f141,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f59,f136])).

% (14259)Refutation not found, incomplete strategy% (14259)------------------------------
% (14259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14261)Refutation not found, incomplete strategy% (14261)------------------------------
% (14261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14261)Termination reason: Refutation not found, incomplete strategy

% (14261)Memory used [KB]: 10618
% (14261)Time elapsed: 0.156 s
% (14261)------------------------------
% (14261)------------------------------
% (14259)Termination reason: Refutation not found, incomplete strategy

% (14259)Memory used [KB]: 1918
% (14259)Time elapsed: 0.135 s
% (14259)------------------------------
% (14259)------------------------------
fof(f136,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f134,f91])).

fof(f91,plain,(
    ! [X8] : k11_relat_1(sK1,X8) = k9_relat_1(sK1,k1_tarski(X8)) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f134,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f132,f84])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK0),X0)
      | k2_relat_1(sK1) = k9_relat_1(sK1,X0) ) ),
    inference(forward_demodulation,[],[f131,f85])).

fof(f85,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f48,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f131,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) = k2_relat_1(k7_relat_1(sK1,X0))
      | ~ r1_tarski(k1_tarski(sK0),X0) ) ),
    inference(forward_demodulation,[],[f130,f92])).

fof(f92,plain,(
    ! [X9] : k7_relat_1(sK1,X9) = k5_relat_1(k6_relat_1(X9),sK1) ),
    inference(resolution,[],[f48,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK0),X0)
      | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ) ),
    inference(forward_demodulation,[],[f128,f58])).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK0),k2_relat_1(k6_relat_1(X0)))
      | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ) ),
    inference(resolution,[],[f93,f77])).

fof(f77,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f93,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_tarski(sK0),k2_relat_1(X2))
      | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(X2,sK1)) ) ),
    inference(forward_demodulation,[],[f87,f50])).

fof(f87,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(X2))
      | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(X2,sK1)) ) ),
    inference(resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f245,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(superposition,[],[f62,f164])).

fof(f164,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0)
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f160,f152])).

fof(f160,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f139,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f139,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X1 ) ),
    inference(superposition,[],[f103,f136])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(resolution,[],[f100,f90])).

fof(f90,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X7,X6),sK1)
      | ~ r2_hidden(X6,k11_relat_1(sK1,X7)) ) ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f96,f48])).

fof(f96,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (14260)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (14269)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (14247)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (14252)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (14245)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (14245)Refutation not found, incomplete strategy% (14245)------------------------------
% 0.20/0.52  % (14245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14245)Memory used [KB]: 1663
% 0.20/0.52  % (14245)Time elapsed: 0.103 s
% 0.20/0.52  % (14245)------------------------------
% 0.20/0.52  % (14245)------------------------------
% 0.20/0.52  % (14272)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (14259)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (14250)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (14268)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (14251)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14273)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (14248)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  % (14261)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.54  % (14271)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (14275)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (14246)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.54  % (14275)Refutation not found, incomplete strategy% (14275)------------------------------
% 1.33/0.54  % (14275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (14262)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.54  % (14258)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.54  % (14270)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.54  % (14274)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.54  % (14263)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.54  % (14265)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.54  % (14255)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.55  % (14275)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (14275)Memory used [KB]: 1663
% 1.33/0.55  % (14275)Time elapsed: 0.128 s
% 1.33/0.55  % (14275)------------------------------
% 1.33/0.55  % (14275)------------------------------
% 1.33/0.55  % (14263)Refutation found. Thanks to Tanya!
% 1.33/0.55  % SZS status Theorem for theBenchmark
% 1.33/0.55  % (14264)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (14257)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.55  % (14256)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.55  % (14244)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.55  % (14253)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.55  % (14254)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.56  % (14267)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.56  % (14257)Refutation not found, incomplete strategy% (14257)------------------------------
% 1.48/0.56  % (14257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (14257)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (14257)Memory used [KB]: 10746
% 1.48/0.56  % (14257)Time elapsed: 0.149 s
% 1.48/0.56  % (14257)------------------------------
% 1.48/0.56  % (14257)------------------------------
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f250,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(subsumption_resolution,[],[f249,f51])).
% 1.48/0.56  fof(f51,plain,(
% 1.48/0.56    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.48/0.56    inference(cnf_transformation,[],[f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.48/0.56    inference(flattening,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.48/0.56    inference(ennf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.48/0.56    inference(negated_conjecture,[],[f21])).
% 1.48/0.56  fof(f21,conjecture,(
% 1.48/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.48/0.56  fof(f249,plain,(
% 1.48/0.56    k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0))),
% 1.48/0.56    inference(equality_resolution,[],[f248])).
% 1.48/0.56  fof(f248,plain,(
% 1.48/0.56    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f245,f152])).
% 1.48/0.56  fof(f152,plain,(
% 1.48/0.56    k1_xboole_0 != k2_relat_1(sK1)),
% 1.48/0.56    inference(subsumption_resolution,[],[f151,f84])).
% 1.48/0.56  fof(f84,plain,(
% 1.48/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.56    inference(equality_resolution,[],[f73])).
% 1.48/0.56  fof(f73,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.48/0.56    inference(cnf_transformation,[],[f47])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.56    inference(flattening,[],[f46])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.56    inference(nnf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.56  fof(f151,plain,(
% 1.48/0.56    k1_xboole_0 != k2_relat_1(sK1) | ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 1.48/0.56    inference(resolution,[],[f143,f63])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f42])).
% 1.48/0.56  fof(f42,plain,(
% 1.48/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.48/0.56    inference(nnf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.48/0.56  fof(f143,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 != k2_relat_1(sK1)),
% 1.48/0.56    inference(forward_demodulation,[],[f142,f50])).
% 1.48/0.56  fof(f50,plain,(
% 1.48/0.56    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f36])).
% 1.48/0.56  fof(f142,plain,(
% 1.48/0.56    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.48/0.56    inference(subsumption_resolution,[],[f141,f48])).
% 1.48/0.56  fof(f48,plain,(
% 1.48/0.56    v1_relat_1(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f36])).
% 1.48/0.56  fof(f141,plain,(
% 1.48/0.56    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.48/0.56    inference(superposition,[],[f59,f136])).
% 1.48/0.56  % (14259)Refutation not found, incomplete strategy% (14259)------------------------------
% 1.48/0.56  % (14259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (14261)Refutation not found, incomplete strategy% (14261)------------------------------
% 1.48/0.56  % (14261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (14261)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (14261)Memory used [KB]: 10618
% 1.48/0.56  % (14261)Time elapsed: 0.156 s
% 1.48/0.56  % (14261)------------------------------
% 1.48/0.56  % (14261)------------------------------
% 1.48/0.56  % (14259)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (14259)Memory used [KB]: 1918
% 1.48/0.56  % (14259)Time elapsed: 0.135 s
% 1.48/0.56  % (14259)------------------------------
% 1.48/0.56  % (14259)------------------------------
% 1.48/0.57  fof(f136,plain,(
% 1.48/0.57    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 1.48/0.57    inference(superposition,[],[f134,f91])).
% 1.48/0.57  fof(f91,plain,(
% 1.48/0.57    ( ! [X8] : (k11_relat_1(sK1,X8) = k9_relat_1(sK1,k1_tarski(X8))) )),
% 1.48/0.57    inference(resolution,[],[f48,f71])).
% 1.48/0.57  fof(f71,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f33])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.48/0.57  fof(f134,plain,(
% 1.48/0.57    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))),
% 1.48/0.57    inference(resolution,[],[f132,f84])).
% 1.48/0.57  fof(f132,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),X0) | k2_relat_1(sK1) = k9_relat_1(sK1,X0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f131,f85])).
% 1.48/0.57  fof(f85,plain,(
% 1.48/0.57    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 1.48/0.57    inference(resolution,[],[f48,f55])).
% 1.48/0.57  fof(f55,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f27])).
% 1.48/0.57  fof(f27,plain,(
% 1.48/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,axiom,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.48/0.57  fof(f131,plain,(
% 1.48/0.57    ( ! [X0] : (k2_relat_1(sK1) = k2_relat_1(k7_relat_1(sK1,X0)) | ~r1_tarski(k1_tarski(sK0),X0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f130,f92])).
% 1.48/0.57  fof(f92,plain,(
% 1.48/0.57    ( ! [X9] : (k7_relat_1(sK1,X9) = k5_relat_1(k6_relat_1(X9),sK1)) )),
% 1.48/0.57    inference(resolution,[],[f48,f72])).
% 1.48/0.57  fof(f72,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f34])).
% 1.48/0.57  fof(f34,plain,(
% 1.48/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f19])).
% 1.48/0.57  fof(f19,axiom,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.48/0.57  fof(f130,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),X0) | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) )),
% 1.48/0.57    inference(forward_demodulation,[],[f128,f58])).
% 1.48/0.57  fof(f58,plain,(
% 1.48/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f18])).
% 1.48/0.57  fof(f18,axiom,(
% 1.48/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.48/0.57  fof(f128,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),k2_relat_1(k6_relat_1(X0))) | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) )),
% 1.48/0.57    inference(resolution,[],[f93,f77])).
% 1.48/0.57  fof(f77,plain,(
% 1.48/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f13])).
% 1.48/0.57  fof(f13,axiom,(
% 1.48/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.48/0.57  fof(f93,plain,(
% 1.48/0.57    ( ! [X2] : (~v1_relat_1(X2) | ~r1_tarski(k1_tarski(sK0),k2_relat_1(X2)) | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(X2,sK1))) )),
% 1.48/0.57    inference(forward_demodulation,[],[f87,f50])).
% 1.48/0.57  fof(f87,plain,(
% 1.48/0.57    ( ! [X2] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(sK1),k2_relat_1(X2)) | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(X2,sK1))) )),
% 1.48/0.57    inference(resolution,[],[f48,f56])).
% 1.48/0.57  fof(f56,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f29])).
% 1.48/0.57  fof(f29,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(flattening,[],[f28])).
% 1.48/0.57  fof(f28,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 1.48/0.57  fof(f59,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f39])).
% 1.48/0.57  fof(f39,plain,(
% 1.48/0.57    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(nnf_transformation,[],[f30])).
% 1.48/0.57  fof(f30,plain,(
% 1.48/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,axiom,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 1.48/0.57  fof(f245,plain,(
% 1.48/0.57    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f244])).
% 1.48/0.57  fof(f244,plain,(
% 1.48/0.57    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 1.48/0.57    inference(superposition,[],[f62,f164])).
% 1.48/0.57  fof(f164,plain,(
% 1.48/0.57    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0) | k1_tarski(X0) = k2_relat_1(sK1)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f160,f152])).
% 1.48/0.57  fof(f160,plain,(
% 1.48/0.57    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X0) = k2_relat_1(sK1)) )),
% 1.48/0.57    inference(resolution,[],[f139,f61])).
% 1.48/0.57  fof(f61,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f41])).
% 1.48/0.57  fof(f41,plain,(
% 1.48/0.57    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f40])).
% 1.48/0.57  fof(f40,plain,(
% 1.48/0.57    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f31,plain,(
% 1.48/0.57    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.48/0.57    inference(ennf_transformation,[],[f11])).
% 1.48/0.57  fof(f11,axiom,(
% 1.48/0.57    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.48/0.57  fof(f139,plain,(
% 1.48/0.57    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X1) )),
% 1.48/0.57    inference(superposition,[],[f103,f136])).
% 1.48/0.57  fof(f103,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) )),
% 1.48/0.57    inference(resolution,[],[f100,f90])).
% 1.48/0.57  fof(f90,plain,(
% 1.48/0.57    ( ! [X6,X7] : (r2_hidden(k4_tarski(X7,X6),sK1) | ~r2_hidden(X6,k11_relat_1(sK1,X7))) )),
% 1.48/0.57    inference(resolution,[],[f48,f70])).
% 1.48/0.57  fof(f70,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f45])).
% 1.48/0.57  fof(f45,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(nnf_transformation,[],[f32])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(ennf_transformation,[],[f15])).
% 1.48/0.57  fof(f15,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.48/0.57  fof(f100,plain,(
% 1.48/0.57    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f96,f48])).
% 1.48/0.57  fof(f96,plain,(
% 1.48/0.57    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3 | ~v1_relat_1(sK1)) )),
% 1.48/0.57    inference(resolution,[],[f49,f53])).
% 1.48/0.57  fof(f53,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f38])).
% 1.48/0.57  fof(f38,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(flattening,[],[f37])).
% 1.48/0.57  fof(f37,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(nnf_transformation,[],[f26])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.48/0.57    inference(flattening,[],[f25])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f20])).
% 1.48/0.57  fof(f20,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.48/0.57  fof(f49,plain,(
% 1.48/0.57    v1_funct_1(sK1)),
% 1.48/0.57    inference(cnf_transformation,[],[f36])).
% 1.48/0.57  fof(f62,plain,(
% 1.48/0.57    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f41])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (14263)------------------------------
% 1.48/0.57  % (14263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (14263)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (14263)Memory used [KB]: 1791
% 1.48/0.57  % (14263)Time elapsed: 0.145 s
% 1.48/0.57  % (14263)------------------------------
% 1.48/0.57  % (14263)------------------------------
% 1.48/0.57  % (14241)Success in time 0.207 s
%------------------------------------------------------------------------------
