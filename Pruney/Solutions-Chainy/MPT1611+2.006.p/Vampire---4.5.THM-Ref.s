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
% DateTime   : Thu Dec  3 13:16:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 124 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  253 ( 430 expanded)
%              Number of equality atoms :  123 ( 205 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f133,f504,f135])).

fof(f135,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k9_setfam_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f95,f71])).

fof(f71,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK8(X0,X1),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r1_tarski(sK8(X0,X1),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK8(X0,X1),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( r1_tarski(sK8(X0,X1),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f504,plain,(
    ~ r2_hidden(sK2,k9_setfam_1(sK2)) ),
    inference(forward_demodulation,[],[f503,f127])).

fof(f127,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f72,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f503,plain,(
    ~ r2_hidden(k3_tarski(k9_setfam_1(sK2)),k9_setfam_1(sK2)) ),
    inference(subsumption_resolution,[],[f502,f127])).

fof(f502,plain,
    ( sK2 != k3_tarski(k9_setfam_1(sK2))
    | ~ r2_hidden(k3_tarski(k9_setfam_1(sK2)),k9_setfam_1(sK2)) ),
    inference(superposition,[],[f126,f288])).

fof(f288,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0) ) ),
    inference(subsumption_resolution,[],[f287,f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f231,f213])).

fof(f213,plain,(
    ! [X5] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X5) ),
    inference(subsumption_resolution,[],[f211,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f109,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t203_relat_1)).

fof(f211,plain,(
    ! [X5] :
      ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X5)
      | r2_hidden(X5,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f90,f158])).

fof(f158,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f142,f157])).

fof(f157,plain,(
    ! [X1] : k1_xboole_0 = sK9(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f155,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK9(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK9(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK9(X0,X1)),X0)
        & k1_relat_1(sK9(X0,X1)) = X1
        & v1_funct_1(sK9(X0,X1))
        & v1_relat_1(sK9(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1)),X0)
        & k1_relat_1(sK9(X0,X1)) = X1
        & v1_funct_1(sK9(X0,X1))
        & v1_relat_1(sK9(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f155,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relat_1(sK9(X1,k1_xboole_0))
      | k1_xboole_0 = sK9(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f76,f142])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f142,plain,(
    ! [X0] : v1_relat_1(sK9(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK9(X0,X1))
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f231,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(k1_xboole_0,X1)
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f196,f182])).

fof(f182,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f154,f82])).

fof(f82,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(f154,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK4(X0))
      | k1_xboole_0 = sK4(X0) ) ),
    inference(resolution,[],[f76,f80])).

fof(f80,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f196,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(sK4(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f193,f82])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4(X1)))
      | k1_xboole_0 != k11_relat_1(sK4(X1),X0) ) ),
    inference(resolution,[],[f89,f80])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 != k11_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f287,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f74,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f126,plain,(
    sK2 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK2))) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f68,plain,(
    sK2 != k4_yellow_0(k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    sK2 != k4_yellow_0(k3_yellow_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).

fof(f36,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK2 != k4_yellow_0(k3_yellow_1(sK2)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

fof(f133,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (2870)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.50  % (2883)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (2878)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.50  % (2875)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  % (2875)Refutation not found, incomplete strategy% (2875)------------------------------
% 0.19/0.50  % (2875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2875)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2875)Memory used [KB]: 1663
% 0.19/0.51  % (2875)Time elapsed: 0.052 s
% 0.19/0.51  % (2875)------------------------------
% 0.19/0.51  % (2875)------------------------------
% 0.19/0.51  % (2867)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (2886)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.51  % (2865)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (2863)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (2886)Refutation not found, incomplete strategy% (2886)------------------------------
% 0.19/0.52  % (2886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2878)Refutation not found, incomplete strategy% (2878)------------------------------
% 0.19/0.52  % (2878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2886)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2886)Memory used [KB]: 6140
% 0.19/0.52  % (2886)Time elapsed: 0.105 s
% 0.19/0.52  % (2886)------------------------------
% 0.19/0.52  % (2886)------------------------------
% 0.19/0.52  % (2878)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2878)Memory used [KB]: 1791
% 0.19/0.52  % (2878)Time elapsed: 0.113 s
% 0.19/0.52  % (2878)------------------------------
% 0.19/0.52  % (2878)------------------------------
% 0.19/0.52  % (2862)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (2861)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (2862)Refutation not found, incomplete strategy% (2862)------------------------------
% 0.19/0.53  % (2862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2862)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2862)Memory used [KB]: 1663
% 0.19/0.53  % (2862)Time elapsed: 0.114 s
% 0.19/0.53  % (2862)------------------------------
% 0.19/0.53  % (2862)------------------------------
% 0.19/0.53  % (2879)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (2879)Refutation not found, incomplete strategy% (2879)------------------------------
% 0.19/0.53  % (2879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2879)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2879)Memory used [KB]: 1663
% 0.19/0.53  % (2879)Time elapsed: 0.127 s
% 0.19/0.53  % (2879)------------------------------
% 0.19/0.53  % (2879)------------------------------
% 0.19/0.53  % (2883)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f505,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f133,f504,f135])).
% 0.19/0.53  fof(f135,plain,(
% 0.19/0.53    ( ! [X0,X3] : (r2_hidden(X3,k9_setfam_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f130])).
% 0.19/0.53  fof(f130,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k9_setfam_1(X0) != X1) )),
% 0.19/0.53    inference(definition_unfolding,[],[f95,f71])).
% 0.19/0.53  fof(f71,plain,(
% 0.19/0.53    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,axiom,(
% 0.19/0.53    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.19/0.53  fof(f95,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r1_tarski(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).
% 0.19/0.53  fof(f54,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r1_tarski(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.53    inference(rectify,[],[f52])).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.53  fof(f504,plain,(
% 0.19/0.53    ~r2_hidden(sK2,k9_setfam_1(sK2))),
% 0.19/0.53    inference(forward_demodulation,[],[f503,f127])).
% 0.19/0.53  fof(f127,plain,(
% 0.19/0.53    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f72,f71])).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.19/0.53  fof(f503,plain,(
% 0.19/0.53    ~r2_hidden(k3_tarski(k9_setfam_1(sK2)),k9_setfam_1(sK2))),
% 0.19/0.53    inference(subsumption_resolution,[],[f502,f127])).
% 0.19/0.53  fof(f502,plain,(
% 0.19/0.53    sK2 != k3_tarski(k9_setfam_1(sK2)) | ~r2_hidden(k3_tarski(k9_setfam_1(sK2)),k9_setfam_1(sK2))),
% 0.19/0.53    inference(superposition,[],[f126,f288])).
% 0.19/0.53  fof(f288,plain,(
% 0.19/0.53    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f287,f232])).
% 0.19/0.53  fof(f232,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_xboole_0 != X0) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f231,f213])).
% 0.19/0.53  fof(f213,plain,(
% 0.19/0.53    ( ! [X5] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X5)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f211,f183])).
% 0.19/0.53  fof(f183,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X1) | ~r2_hidden(X1,X0)) )),
% 0.19/0.53    inference(superposition,[],[f109,f137])).
% 0.19/0.53  fof(f137,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f100])).
% 0.19/0.53  fof(f100,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f57])).
% 0.19/0.53  fof(f57,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.53    inference(flattening,[],[f56])).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.53    inference(nnf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.53  fof(f109,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 | ~r2_hidden(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 | ~r2_hidden(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (r2_hidden(X0,X1) => k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t203_relat_1)).
% 0.19/0.53  fof(f211,plain,(
% 0.19/0.53    ( ! [X5] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X5) | r2_hidden(X5,k1_relat_1(k1_xboole_0))) )),
% 0.19/0.53    inference(resolution,[],[f90,f158])).
% 0.19/0.53  fof(f158,plain,(
% 0.19/0.53    v1_relat_1(k1_xboole_0)),
% 0.19/0.53    inference(backward_demodulation,[],[f142,f157])).
% 0.19/0.53  fof(f157,plain,(
% 0.19/0.53    ( ! [X1] : (k1_xboole_0 = sK9(X1,k1_xboole_0)) )),
% 0.19/0.53    inference(subsumption_resolution,[],[f155,f140])).
% 0.19/0.53  fof(f140,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK9(X0,k1_xboole_0))) )),
% 0.19/0.53    inference(equality_resolution,[],[f106])).
% 0.19/0.53  fof(f106,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_relat_1(sK9(X0,X1)) = X1 | k1_xboole_0 != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f59])).
% 0.19/0.53  fof(f59,plain,(
% 0.19/0.53    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK9(X0,X1)),X0) & k1_relat_1(sK9(X0,X1)) = X1 & v1_funct_1(sK9(X0,X1)) & v1_relat_1(sK9(X0,X1))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f58])).
% 0.19/0.53  fof(f58,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK9(X0,X1)),X0) & k1_relat_1(sK9(X0,X1)) = X1 & v1_funct_1(sK9(X0,X1)) & v1_relat_1(sK9(X0,X1))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.19/0.53    inference(flattening,[],[f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & (v1_funct_1(X2) & v1_relat_1(X2))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,axiom,(
% 0.19/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.19/0.53  fof(f155,plain,(
% 0.19/0.53    ( ! [X1] : (k1_xboole_0 != k1_relat_1(sK9(X1,k1_xboole_0)) | k1_xboole_0 = sK9(X1,k1_xboole_0)) )),
% 0.19/0.53    inference(resolution,[],[f76,f142])).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.53    inference(flattening,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,axiom,(
% 0.19/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.53  fof(f142,plain,(
% 0.19/0.53    ( ! [X0] : (v1_relat_1(sK9(X0,k1_xboole_0))) )),
% 0.19/0.53    inference(equality_resolution,[],[f102])).
% 0.19/0.53  fof(f102,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v1_relat_1(sK9(X0,X1)) | k1_xboole_0 != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f59])).
% 0.19/0.53  fof(f90,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f49])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.19/0.53  fof(f231,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(k1_xboole_0,X1) | ~r2_hidden(X1,X0) | k1_xboole_0 != X0) )),
% 0.19/0.53    inference(superposition,[],[f196,f182])).
% 0.19/0.53  fof(f182,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = sK4(X0) | k1_xboole_0 != X0) )),
% 0.19/0.53    inference(superposition,[],[f154,f82])).
% 0.19/0.53  fof(f82,plain,(
% 0.19/0.53    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f41])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f40])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,axiom,(
% 0.19/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).
% 0.19/0.53  fof(f154,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK4(X0)) | k1_xboole_0 = sK4(X0)) )),
% 0.19/0.53    inference(resolution,[],[f76,f80])).
% 0.19/0.53  fof(f80,plain,(
% 0.19/0.53    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f41])).
% 0.19/0.53  fof(f196,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(sK4(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.53    inference(forward_demodulation,[],[f193,f82])).
% 0.19/0.53  fof(f193,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK4(X1))) | k1_xboole_0 != k11_relat_1(sK4(X1),X0)) )),
% 0.19/0.53    inference(resolution,[],[f89,f80])).
% 0.19/0.53  fof(f89,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 != k11_relat_1(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f49])).
% 0.19/0.53  fof(f287,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(resolution,[],[f74,f75])).
% 0.19/0.53  fof(f75,plain,(
% 0.19/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.19/0.53  fof(f74,plain,(
% 0.19/0.53    ( ! [X0] : (v1_xboole_0(X0) | ~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.19/0.53    inference(flattening,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,axiom,(
% 0.19/0.53    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    sK2 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK2)))),
% 0.19/0.53    inference(definition_unfolding,[],[f68,f73])).
% 0.19/0.53  fof(f73,plain,(
% 0.19/0.53    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,axiom,(
% 0.19/0.53    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.19/0.53  fof(f68,plain,(
% 0.19/0.53    sK2 != k4_yellow_0(k3_yellow_1(sK2))),
% 0.19/0.53    inference(cnf_transformation,[],[f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    sK2 != k4_yellow_0(k3_yellow_1(sK2))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK2 != k4_yellow_0(k3_yellow_1(sK2))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.19/0.53    inference(ennf_transformation,[],[f19])).
% 0.19/0.53  fof(f19,negated_conjecture,(
% 0.19/0.53    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.19/0.53    inference(negated_conjecture,[],[f18])).
% 0.19/0.53  fof(f18,conjecture,(
% 0.19/0.53    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.19/0.53  fof(f133,plain,(
% 0.19/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.53    inference(equality_resolution,[],[f92])).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f51])).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.53    inference(flattening,[],[f50])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (2883)------------------------------
% 0.19/0.53  % (2883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2883)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (2883)Memory used [KB]: 6524
% 0.19/0.53  % (2883)Time elapsed: 0.066 s
% 0.19/0.53  % (2883)------------------------------
% 0.19/0.53  % (2883)------------------------------
% 0.19/0.53  % (2890)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (2872)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.53  % (2860)Success in time 0.175 s
%------------------------------------------------------------------------------
