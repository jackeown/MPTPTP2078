%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:18 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  152 (1008 expanded)
%              Number of leaves         :   29 ( 257 expanded)
%              Depth                    :   34
%              Number of atoms          :  437 (3370 expanded)
%              Number of equality atoms :  146 (1192 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1261,plain,(
    $false ),
    inference(resolution,[],[f1250,f213])).

fof(f213,plain,(
    ! [X0] : sP8(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( sP8(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP8(X0,X1) )
      & ( sP8(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP8(X0,X1) ) ),
    inference(definition_folding,[],[f4,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP8(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1250,plain,(
    ! [X3] : ~ sP8(X3,k1_tarski(sK9)) ),
    inference(resolution,[],[f1219,f212])).

fof(f212,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP8(X3,X1) ) ),
    inference(equality_resolution,[],[f185])).

fof(f185,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ( ( sK19(X0,X1) != X0
            | ~ r2_hidden(sK19(X0,X1),X1) )
          & ( sK19(X0,X1) = X0
            | r2_hidden(sK19(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP8(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f117,f118])).

fof(f118,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK19(X0,X1) != X0
          | ~ r2_hidden(sK19(X0,X1),X1) )
        & ( sK19(X0,X1) = X0
          | r2_hidden(sK19(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP8(X0,X1) ) ) ),
    inference(rectify,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP8(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f83])).

fof(f1219,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_tarski(sK9)) ),
    inference(subsumption_resolution,[],[f1203,f504])).

fof(f504,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f495,f352])).

fof(f352,plain,(
    ! [X10] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X10) ),
    inference(forward_demodulation,[],[f351,f133])).

fof(f133,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f351,plain,(
    ! [X10] : k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(k1_xboole_0),X10) ),
    inference(forward_demodulation,[],[f328,f136])).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f328,plain,(
    ! [X10] : k3_xboole_0(k1_relat_1(k1_xboole_0),X10) = k1_relat_1(k7_relat_1(k1_xboole_0,X10)) ),
    inference(resolution,[],[f315,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f315,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f313,f243])).

fof(f243,plain,(
    v1_relat_1(sK11) ),
    inference(resolution,[],[f130,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f130,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( k2_relset_1(k1_tarski(sK9),sK10,sK11) != k1_tarski(k1_funct_1(sK11,sK9))
    & k1_xboole_0 != sK10
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))
    & v1_funct_2(sK11,k1_tarski(sK9),sK10)
    & v1_funct_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f37,f85])).

fof(f85,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK9),sK10,sK11) != k1_tarski(k1_funct_1(sK11,sK9))
      & k1_xboole_0 != sK10
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))
      & v1_funct_2(sK11,k1_tarski(sK9),sK10)
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f313,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK11) ),
    inference(superposition,[],[f267,f138])).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f267,plain,(
    ! [X10] : v1_relat_1(k7_relat_1(sK11,X10)) ),
    inference(resolution,[],[f243,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f495,plain,(
    ! [X2,X1] : ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(resolution,[],[f485,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK16(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f48,f109])).

fof(f109,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK16(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f485,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    inference(trivial_inequality_removal,[],[f480])).

fof(f480,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f183,f352])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1203,plain,(
    ! [X2] :
      ( r2_hidden(k1_funct_1(sK11,X2),k1_xboole_0)
      | ~ r2_hidden(X2,k1_tarski(sK9)) ) ),
    inference(backward_demodulation,[],[f878,f1195])).

fof(f1195,plain,(
    k1_xboole_0 = k2_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f1179,f1133])).

fof(f1133,plain,(
    k2_relat_1(sK11) != k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f290,f1124])).

fof(f1124,plain,(
    k1_xboole_0 = k1_funct_1(sK11,sK9) ),
    inference(subsumption_resolution,[],[f1117,f366])).

fof(f366,plain,(
    ! [X2,X3] : sP4(X2,X3,sK11) ),
    inference(subsumption_resolution,[],[f220,f243])).

fof(f220,plain,(
    ! [X2,X3] :
      ( sP4(X2,X3,sK11)
      | ~ v1_relat_1(sK11) ) ),
    inference(resolution,[],[f128,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X2,X1,X0)
          & sP3(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f45,f77,f76])).

fof(f76,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f128,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f86])).

fof(f1117,plain,
    ( k1_xboole_0 = k1_funct_1(sK11,sK9)
    | ~ sP4(k1_funct_1(sK11,sK9),sK9,sK11) ),
    inference(resolution,[],[f1112,f208])).

fof(f208,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_funct_1(X2,X1)
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP4(k1_funct_1(X2,X1),X1,X2) ) ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_funct_1(X2,X1) != X0
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X2,X1) = X0
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | k1_funct_1(X2,X1) != X0 ) )
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X2,X1,X0] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | k1_funct_1(X0,X1) != X2 ) )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f1112,plain,(
    ~ r2_hidden(sK9,k1_relat_1(sK11)) ),
    inference(subsumption_resolution,[],[f1111,f243])).

fof(f1111,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f1110,f128])).

fof(f1110,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK11))
    | ~ v1_funct_1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f1105,f290])).

fof(f1105,plain,
    ( k1_tarski(k1_funct_1(sK11,sK9)) = k2_relat_1(sK11)
    | ~ r2_hidden(sK9,k1_relat_1(sK11))
    | ~ v1_funct_1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(superposition,[],[f181,f1089])).

fof(f1089,plain,(
    sK11 = k7_relat_1(sK11,k1_tarski(sK9)) ),
    inference(subsumption_resolution,[],[f1082,f243])).

fof(f1082,plain,
    ( sK11 = k7_relat_1(sK11,k1_tarski(sK9))
    | ~ v1_relat_1(sK11) ),
    inference(resolution,[],[f1079,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f1079,plain,(
    r1_tarski(k1_relat_1(sK11),k1_tarski(sK9)) ),
    inference(subsumption_resolution,[],[f1078,f524])).

fof(f524,plain,(
    ! [X4] : k1_xboole_0 != k1_tarski(X4) ),
    inference(forward_demodulation,[],[f507,f352])).

fof(f507,plain,(
    ! [X4] : k1_tarski(X4) != k3_xboole_0(k1_xboole_0,k1_tarski(X4)) ),
    inference(resolution,[],[f504,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f1078,plain,
    ( r1_tarski(k1_relat_1(sK11),k1_tarski(sK9))
    | k1_xboole_0 = k1_tarski(sK9) ),
    inference(subsumption_resolution,[],[f1075,f131])).

fof(f131,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f86])).

fof(f1075,plain,
    ( r1_tarski(k1_relat_1(sK11),k1_tarski(sK9))
    | k1_xboole_0 = sK10
    | k1_xboole_0 = k1_tarski(sK9) ),
    inference(superposition,[],[f379,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f379,plain,(
    r1_tarski(k1_relat_1(sK11),k1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) ),
    inference(subsumption_resolution,[],[f378,f243])).

fof(f378,plain,
    ( r1_tarski(k1_relat_1(sK11),k1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))
    | ~ v1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f374,f168])).

fof(f168,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f374,plain,
    ( r1_tarski(k1_relat_1(sK11),k1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10))
    | ~ v1_relat_1(sK11) ),
    inference(resolution,[],[f244,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f244,plain,(
    r1_tarski(sK11,k2_zfmisc_1(k1_tarski(sK9),sK10)) ),
    inference(resolution,[],[f130,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f181,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(f290,plain,(
    k1_tarski(k1_funct_1(sK11,sK9)) != k2_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f289,f130])).

fof(f289,plain,
    ( k1_tarski(k1_funct_1(sK11,sK9)) != k2_relat_1(sK11)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) ),
    inference(superposition,[],[f132,f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f132,plain,(
    k2_relset_1(k1_tarski(sK9),sK10,sK11) != k1_tarski(k1_funct_1(sK11,sK9)) ),
    inference(cnf_transformation,[],[f86])).

fof(f1179,plain,
    ( k2_relat_1(sK11) = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK11) ),
    inference(resolution,[],[f1172,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f1172,plain,(
    r1_tarski(k2_relat_1(sK11),k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1166,f1124])).

fof(f1166,plain,(
    r1_tarski(k2_relat_1(sK11),k1_tarski(k1_funct_1(sK11,sK9))) ),
    inference(superposition,[],[f1009,f1100])).

fof(f1100,plain,(
    k2_relat_1(sK11) = k9_relat_1(sK11,k1_tarski(sK9)) ),
    inference(superposition,[],[f268,f1089])).

fof(f268,plain,(
    ! [X11] : k9_relat_1(sK11,X11) = k2_relat_1(k7_relat_1(sK11,X11)) ),
    inference(resolution,[],[f243,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1009,plain,(
    ! [X4] : r1_tarski(k9_relat_1(sK11,k1_tarski(X4)),k1_tarski(k1_funct_1(sK11,X4))) ),
    inference(backward_demodulation,[],[f681,f268])).

fof(f681,plain,(
    ! [X4] : r1_tarski(k2_relat_1(k7_relat_1(sK11,k1_tarski(X4))),k1_tarski(k1_funct_1(sK11,X4))) ),
    inference(subsumption_resolution,[],[f222,f243])).

fof(f222,plain,(
    ! [X4] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK11,k1_tarski(X4))),k1_tarski(k1_funct_1(sK11,X4)))
      | ~ v1_relat_1(sK11) ) ),
    inference(resolution,[],[f128,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f878,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tarski(sK9))
      | r2_hidden(k1_funct_1(sK11,X2),k2_relat_1(sK11)) ) ),
    inference(forward_demodulation,[],[f253,f242])).

fof(f242,plain,(
    k2_relset_1(k1_tarski(sK9),sK10,sK11) = k2_relat_1(sK11) ),
    inference(resolution,[],[f130,f201])).

fof(f253,plain,(
    ! [X2] :
      ( r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11))
      | ~ r2_hidden(X2,k1_tarski(sK9)) ) ),
    inference(subsumption_resolution,[],[f252,f128])).

fof(f252,plain,(
    ! [X2] :
      ( r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11))
      | ~ r2_hidden(X2,k1_tarski(sK9))
      | ~ v1_funct_1(sK11) ) ),
    inference(subsumption_resolution,[],[f251,f129])).

fof(f129,plain,(
    v1_funct_2(sK11,k1_tarski(sK9),sK10) ),
    inference(cnf_transformation,[],[f86])).

fof(f251,plain,(
    ! [X2] :
      ( r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11))
      | ~ r2_hidden(X2,k1_tarski(sK9))
      | ~ v1_funct_2(sK11,k1_tarski(sK9),sK10)
      | ~ v1_funct_1(sK11) ) ),
    inference(subsumption_resolution,[],[f241,f131])).

fof(f241,plain,(
    ! [X2] :
      ( r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11))
      | k1_xboole_0 = sK10
      | ~ r2_hidden(X2,k1_tarski(sK9))
      | ~ v1_funct_2(sK11,k1_tarski(sK9),sK10)
      | ~ v1_funct_1(sK11) ) ),
    inference(resolution,[],[f130,f202])).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:32:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (29439)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (29436)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (29434)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (29435)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (29438)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (29454)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.20/0.52  % (29431)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.20/0.52  % (29443)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.20/0.52  % (29451)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.20/0.52  % (29433)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.20/0.52  % (29455)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.20/0.52  % (29446)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.20/0.52  % (29449)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.20/0.52  % (29442)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.20/0.52  % (29456)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.20/0.52  % (29444)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.20/0.52  % (29440)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.20/0.53  % (29441)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.53  % (29432)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.53  % (29448)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.33/0.53  % (29437)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.33/0.53  % (29453)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.33/0.54  % (29450)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.33/0.54  % (29447)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.33/0.54  % (29439)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % (29452)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.33/0.55  % (29445)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f1261,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(resolution,[],[f1250,f213])).
% 1.33/0.55  fof(f213,plain,(
% 1.33/0.55    ( ! [X0] : (sP8(X0,k1_tarski(X0))) )),
% 1.33/0.55    inference(equality_resolution,[],[f188])).
% 1.33/0.55  fof(f188,plain,(
% 1.33/0.55    ( ! [X0,X1] : (sP8(X0,X1) | k1_tarski(X0) != X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f120])).
% 1.33/0.55  fof(f120,plain,(
% 1.33/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP8(X0,X1)) & (sP8(X0,X1) | k1_tarski(X0) != X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f84])).
% 1.33/0.55  fof(f84,plain,(
% 1.33/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP8(X0,X1))),
% 1.33/0.55    inference(definition_folding,[],[f4,f83])).
% 1.33/0.55  fof(f83,plain,(
% 1.33/0.55    ! [X0,X1] : (sP8(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.33/0.55  fof(f1250,plain,(
% 1.33/0.55    ( ! [X3] : (~sP8(X3,k1_tarski(sK9))) )),
% 1.33/0.55    inference(resolution,[],[f1219,f212])).
% 1.33/0.55  fof(f212,plain,(
% 1.33/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | ~sP8(X3,X1)) )),
% 1.33/0.55    inference(equality_resolution,[],[f185])).
% 1.33/0.55  fof(f185,plain,(
% 1.33/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | ~sP8(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f119])).
% 1.33/0.55  fof(f119,plain,(
% 1.33/0.55    ! [X0,X1] : ((sP8(X0,X1) | ((sK19(X0,X1) != X0 | ~r2_hidden(sK19(X0,X1),X1)) & (sK19(X0,X1) = X0 | r2_hidden(sK19(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP8(X0,X1)))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f117,f118])).
% 1.33/0.55  fof(f118,plain,(
% 1.33/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK19(X0,X1) != X0 | ~r2_hidden(sK19(X0,X1),X1)) & (sK19(X0,X1) = X0 | r2_hidden(sK19(X0,X1),X1))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f117,plain,(
% 1.33/0.55    ! [X0,X1] : ((sP8(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP8(X0,X1)))),
% 1.33/0.55    inference(rectify,[],[f116])).
% 1.33/0.55  fof(f116,plain,(
% 1.33/0.55    ! [X0,X1] : ((sP8(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP8(X0,X1)))),
% 1.33/0.55    inference(nnf_transformation,[],[f83])).
% 1.33/0.55  fof(f1219,plain,(
% 1.33/0.55    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK9))) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f1203,f504])).
% 1.33/0.55  fof(f504,plain,(
% 1.33/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f495,f352])).
% 1.33/0.55  fof(f352,plain,(
% 1.33/0.55    ( ! [X10] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X10)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f351,f133])).
% 1.33/0.55  fof(f133,plain,(
% 1.33/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(cnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,axiom,(
% 1.33/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.33/0.55  fof(f351,plain,(
% 1.33/0.55    ( ! [X10] : (k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(k1_xboole_0),X10)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f328,f136])).
% 1.33/0.55  fof(f136,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f12])).
% 1.33/0.55  fof(f12,axiom,(
% 1.33/0.55    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 1.33/0.55  fof(f328,plain,(
% 1.33/0.55    ( ! [X10] : (k3_xboole_0(k1_relat_1(k1_xboole_0),X10) = k1_relat_1(k7_relat_1(k1_xboole_0,X10))) )),
% 1.33/0.55    inference(resolution,[],[f315,f173])).
% 1.33/0.55  fof(f173,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f51])).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f21])).
% 1.33/0.55  fof(f21,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.33/0.55  fof(f315,plain,(
% 1.33/0.55    v1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f313,f243])).
% 1.33/0.55  fof(f243,plain,(
% 1.33/0.55    v1_relat_1(sK11)),
% 1.33/0.55    inference(resolution,[],[f130,f200])).
% 1.33/0.55  fof(f200,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f66])).
% 1.33/0.55  fof(f66,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f29])).
% 1.33/0.55  fof(f29,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.33/0.55  fof(f130,plain,(
% 1.33/0.55    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))),
% 1.33/0.55    inference(cnf_transformation,[],[f86])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    k2_relset_1(k1_tarski(sK9),sK10,sK11) != k1_tarski(k1_funct_1(sK11,sK9)) & k1_xboole_0 != sK10 & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) & v1_funct_2(sK11,k1_tarski(sK9),sK10) & v1_funct_1(sK11)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f37,f85])).
% 1.33/0.55  fof(f85,plain,(
% 1.33/0.55    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK9),sK10,sK11) != k1_tarski(k1_funct_1(sK11,sK9)) & k1_xboole_0 != sK10 & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) & v1_funct_2(sK11,k1_tarski(sK9),sK10) & v1_funct_1(sK11))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f37,plain,(
% 1.33/0.55    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.33/0.55    inference(flattening,[],[f36])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.33/0.55    inference(ennf_transformation,[],[f34])).
% 1.33/0.55  fof(f34,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.33/0.55    inference(negated_conjecture,[],[f33])).
% 1.33/0.55  fof(f33,conjecture,(
% 1.33/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.33/0.55  fof(f313,plain,(
% 1.33/0.55    v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(superposition,[],[f267,f138])).
% 1.33/0.55  fof(f138,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f39])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 1.33/0.55  fof(f267,plain,(
% 1.33/0.55    ( ! [X10] : (v1_relat_1(k7_relat_1(sK11,X10))) )),
% 1.33/0.55    inference(resolution,[],[f243,f171])).
% 1.33/0.55  fof(f171,plain,(
% 1.33/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f9])).
% 1.33/0.55  fof(f9,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.33/0.55  fof(f495,plain,(
% 1.33/0.55    ( ! [X2,X1] : (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))) )),
% 1.33/0.55    inference(resolution,[],[f485,f170])).
% 1.33/0.55  fof(f170,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f110])).
% 1.33/0.55  fof(f110,plain,(
% 1.33/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK16(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f48,f109])).
% 1.33/0.55  fof(f109,plain,(
% 1.33/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK16(X0,X1),k3_xboole_0(X0,X1)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(rectify,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.33/0.55  fof(f485,plain,(
% 1.33/0.55    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) )),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f480])).
% 1.33/0.55  fof(f480,plain,(
% 1.33/0.55    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X1)) )),
% 1.33/0.55    inference(superposition,[],[f183,f352])).
% 1.33/0.55  fof(f183,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f115])).
% 1.33/0.55  fof(f115,plain,(
% 1.33/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(nnf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.33/0.55  fof(f1203,plain,(
% 1.33/0.55    ( ! [X2] : (r2_hidden(k1_funct_1(sK11,X2),k1_xboole_0) | ~r2_hidden(X2,k1_tarski(sK9))) )),
% 1.33/0.55    inference(backward_demodulation,[],[f878,f1195])).
% 1.33/0.55  fof(f1195,plain,(
% 1.33/0.55    k1_xboole_0 = k2_relat_1(sK11)),
% 1.33/0.55    inference(subsumption_resolution,[],[f1179,f1133])).
% 1.33/0.55  fof(f1133,plain,(
% 1.33/0.55    k2_relat_1(sK11) != k1_tarski(k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f290,f1124])).
% 1.33/0.55  fof(f1124,plain,(
% 1.33/0.55    k1_xboole_0 = k1_funct_1(sK11,sK9)),
% 1.33/0.55    inference(subsumption_resolution,[],[f1117,f366])).
% 1.33/0.55  fof(f366,plain,(
% 1.33/0.55    ( ! [X2,X3] : (sP4(X2,X3,sK11)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f220,f243])).
% 1.33/0.55  fof(f220,plain,(
% 1.33/0.55    ( ! [X2,X3] : (sP4(X2,X3,sK11) | ~v1_relat_1(sK11)) )),
% 1.33/0.55    inference(resolution,[],[f128,f156])).
% 1.33/0.55  fof(f156,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (sP4(X2,X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f78])).
% 1.33/0.55  fof(f78,plain,(
% 1.33/0.55    ! [X0] : (! [X1,X2] : (sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(definition_folding,[],[f45,f77,f76])).
% 1.33/0.55  fof(f76,plain,(
% 1.33/0.55    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP3(X0,X2,X1))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP4(X2,X1,X0))),
% 1.33/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(flattening,[],[f44])).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.55    inference(ennf_transformation,[],[f25])).
% 1.33/0.55  fof(f25,axiom,(
% 1.33/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.33/0.55  fof(f128,plain,(
% 1.33/0.55    v1_funct_1(sK11)),
% 1.33/0.55    inference(cnf_transformation,[],[f86])).
% 1.33/0.55  fof(f1117,plain,(
% 1.33/0.55    k1_xboole_0 = k1_funct_1(sK11,sK9) | ~sP4(k1_funct_1(sK11,sK9),sK9,sK11)),
% 1.33/0.55    inference(resolution,[],[f1112,f208])).
% 1.33/0.55  fof(f208,plain,(
% 1.33/0.55    ( ! [X2,X1] : (k1_xboole_0 = k1_funct_1(X2,X1) | r2_hidden(X1,k1_relat_1(X2)) | ~sP4(k1_funct_1(X2,X1),X1,X2)) )),
% 1.33/0.55    inference(equality_resolution,[],[f151])).
% 1.33/0.55  fof(f151,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_funct_1(X2,X1) != X0 | r2_hidden(X1,k1_relat_1(X2)) | ~sP4(X0,X1,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f97])).
% 1.33/0.55  fof(f97,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | k1_funct_1(X2,X1) != X0)) | r2_hidden(X1,k1_relat_1(X2)) | ~sP4(X0,X1,X2))),
% 1.33/0.55    inference(rectify,[],[f96])).
% 1.33/0.55  fof(f96,plain,(
% 1.33/0.55    ! [X2,X1,X0] : (((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0)) | ~sP4(X2,X1,X0))),
% 1.33/0.55    inference(nnf_transformation,[],[f77])).
% 1.33/0.55  fof(f1112,plain,(
% 1.33/0.55    ~r2_hidden(sK9,k1_relat_1(sK11))),
% 1.33/0.55    inference(subsumption_resolution,[],[f1111,f243])).
% 1.33/0.55  fof(f1111,plain,(
% 1.33/0.55    ~r2_hidden(sK9,k1_relat_1(sK11)) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(subsumption_resolution,[],[f1110,f128])).
% 1.33/0.55  fof(f1110,plain,(
% 1.33/0.55    ~r2_hidden(sK9,k1_relat_1(sK11)) | ~v1_funct_1(sK11) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(subsumption_resolution,[],[f1105,f290])).
% 1.33/0.55  fof(f1105,plain,(
% 1.33/0.55    k1_tarski(k1_funct_1(sK11,sK9)) = k2_relat_1(sK11) | ~r2_hidden(sK9,k1_relat_1(sK11)) | ~v1_funct_1(sK11) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(superposition,[],[f181,f1089])).
% 1.33/0.55  fof(f1089,plain,(
% 1.33/0.55    sK11 = k7_relat_1(sK11,k1_tarski(sK9))),
% 1.33/0.55    inference(subsumption_resolution,[],[f1082,f243])).
% 1.33/0.55  fof(f1082,plain,(
% 1.33/0.55    sK11 = k7_relat_1(sK11,k1_tarski(sK9)) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(resolution,[],[f1079,f176])).
% 1.33/0.55  fof(f176,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f55])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f54])).
% 1.33/0.55  fof(f54,plain,(
% 1.33/0.55    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f23])).
% 1.33/0.55  fof(f23,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.33/0.55  fof(f1079,plain,(
% 1.33/0.55    r1_tarski(k1_relat_1(sK11),k1_tarski(sK9))),
% 1.33/0.55    inference(subsumption_resolution,[],[f1078,f524])).
% 1.33/0.55  fof(f524,plain,(
% 1.33/0.55    ( ! [X4] : (k1_xboole_0 != k1_tarski(X4)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f507,f352])).
% 1.33/0.55  fof(f507,plain,(
% 1.33/0.55    ( ! [X4] : (k1_tarski(X4) != k3_xboole_0(k1_xboole_0,k1_tarski(X4))) )),
% 1.33/0.55    inference(resolution,[],[f504,f179])).
% 1.33/0.55  fof(f179,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f60])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 1.33/0.55  fof(f1078,plain,(
% 1.33/0.55    r1_tarski(k1_relat_1(sK11),k1_tarski(sK9)) | k1_xboole_0 = k1_tarski(sK9)),
% 1.33/0.55    inference(subsumption_resolution,[],[f1075,f131])).
% 1.33/0.55  fof(f131,plain,(
% 1.33/0.55    k1_xboole_0 != sK10),
% 1.33/0.55    inference(cnf_transformation,[],[f86])).
% 1.33/0.55  fof(f1075,plain,(
% 1.33/0.55    r1_tarski(k1_relat_1(sK11),k1_tarski(sK9)) | k1_xboole_0 = sK10 | k1_xboole_0 = k1_tarski(sK9)),
% 1.33/0.55    inference(superposition,[],[f379,f198])).
% 1.33/0.55  fof(f198,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f65])).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.33/0.55    inference(ennf_transformation,[],[f17])).
% 1.33/0.55  fof(f17,axiom,(
% 1.33/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 1.33/0.55  fof(f379,plain,(
% 1.33/0.55    r1_tarski(k1_relat_1(sK11),k1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))),
% 1.33/0.55    inference(subsumption_resolution,[],[f378,f243])).
% 1.33/0.55  fof(f378,plain,(
% 1.33/0.55    r1_tarski(k1_relat_1(sK11),k1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(subsumption_resolution,[],[f374,f168])).
% 1.33/0.55  fof(f168,plain,(
% 1.33/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.33/0.55  fof(f374,plain,(
% 1.33/0.55    r1_tarski(k1_relat_1(sK11),k1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10))) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK9),sK10)) | ~v1_relat_1(sK11)),
% 1.33/0.55    inference(resolution,[],[f244,f139])).
% 1.33/0.55  fof(f139,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f41])).
% 1.33/0.55  fof(f41,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(flattening,[],[f40])).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.33/0.55  fof(f244,plain,(
% 1.33/0.55    r1_tarski(sK11,k2_zfmisc_1(k1_tarski(sK9),sK10))),
% 1.33/0.55    inference(resolution,[],[f130,f190])).
% 1.33/0.55  fof(f190,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f121])).
% 1.33/0.55  fof(f121,plain,(
% 1.33/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.33/0.55    inference(nnf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.33/0.55  fof(f181,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f64])).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f63])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    ! [X0,X1] : ((k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f28])).
% 1.33/0.55  fof(f28,axiom,(
% 1.33/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).
% 1.33/0.55  fof(f290,plain,(
% 1.33/0.55    k1_tarski(k1_funct_1(sK11,sK9)) != k2_relat_1(sK11)),
% 1.33/0.55    inference(subsumption_resolution,[],[f289,f130])).
% 1.33/0.55  fof(f289,plain,(
% 1.33/0.55    k1_tarski(k1_funct_1(sK11,sK9)) != k2_relat_1(sK11) | ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK9),sK10)))),
% 1.33/0.55    inference(superposition,[],[f132,f201])).
% 1.33/0.55  fof(f201,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f67])).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f30])).
% 1.33/0.55  fof(f30,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.55  fof(f132,plain,(
% 1.33/0.55    k2_relset_1(k1_tarski(sK9),sK10,sK11) != k1_tarski(k1_funct_1(sK11,sK9))),
% 1.33/0.55    inference(cnf_transformation,[],[f86])).
% 1.33/0.55  fof(f1179,plain,(
% 1.33/0.55    k2_relat_1(sK11) = k1_tarski(k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK11)),
% 1.33/0.55    inference(resolution,[],[f1172,f192])).
% 1.33/0.55  fof(f192,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f123])).
% 1.33/0.55  fof(f123,plain,(
% 1.33/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.33/0.55    inference(flattening,[],[f122])).
% 1.33/0.55  fof(f122,plain,(
% 1.33/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.33/0.55    inference(nnf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 1.33/0.55  fof(f1172,plain,(
% 1.33/0.55    r1_tarski(k2_relat_1(sK11),k1_tarski(k1_xboole_0))),
% 1.33/0.55    inference(forward_demodulation,[],[f1166,f1124])).
% 1.33/0.55  fof(f1166,plain,(
% 1.33/0.55    r1_tarski(k2_relat_1(sK11),k1_tarski(k1_funct_1(sK11,sK9)))),
% 1.33/0.55    inference(superposition,[],[f1009,f1100])).
% 1.33/0.55  fof(f1100,plain,(
% 1.33/0.55    k2_relat_1(sK11) = k9_relat_1(sK11,k1_tarski(sK9))),
% 1.33/0.55    inference(superposition,[],[f268,f1089])).
% 1.33/0.55  fof(f268,plain,(
% 1.33/0.55    ( ! [X11] : (k9_relat_1(sK11,X11) = k2_relat_1(k7_relat_1(sK11,X11))) )),
% 1.33/0.55    inference(resolution,[],[f243,f172])).
% 1.33/0.55  fof(f172,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f50])).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f14])).
% 1.33/0.55  fof(f14,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.33/0.55  fof(f1009,plain,(
% 1.33/0.55    ( ! [X4] : (r1_tarski(k9_relat_1(sK11,k1_tarski(X4)),k1_tarski(k1_funct_1(sK11,X4)))) )),
% 1.33/0.55    inference(backward_demodulation,[],[f681,f268])).
% 1.33/0.55  fof(f681,plain,(
% 1.33/0.55    ( ! [X4] : (r1_tarski(k2_relat_1(k7_relat_1(sK11,k1_tarski(X4))),k1_tarski(k1_funct_1(sK11,X4)))) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f222,f243])).
% 1.33/0.55  fof(f222,plain,(
% 1.33/0.55    ( ! [X4] : (r1_tarski(k2_relat_1(k7_relat_1(sK11,k1_tarski(X4))),k1_tarski(k1_funct_1(sK11,X4))) | ~v1_relat_1(sK11)) )),
% 1.33/0.55    inference(resolution,[],[f128,f180])).
% 1.33/0.55  fof(f180,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f62])).
% 1.33/0.55  fof(f62,plain,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f61])).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,axiom,(
% 1.33/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 1.33/0.55  fof(f878,plain,(
% 1.33/0.55    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK9)) | r2_hidden(k1_funct_1(sK11,X2),k2_relat_1(sK11))) )),
% 1.33/0.55    inference(forward_demodulation,[],[f253,f242])).
% 1.33/0.55  fof(f242,plain,(
% 1.33/0.55    k2_relset_1(k1_tarski(sK9),sK10,sK11) = k2_relat_1(sK11)),
% 1.33/0.55    inference(resolution,[],[f130,f201])).
% 1.33/0.55  fof(f253,plain,(
% 1.33/0.55    ( ! [X2] : (r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11)) | ~r2_hidden(X2,k1_tarski(sK9))) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f252,f128])).
% 1.33/0.55  fof(f252,plain,(
% 1.33/0.55    ( ! [X2] : (r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11)) | ~r2_hidden(X2,k1_tarski(sK9)) | ~v1_funct_1(sK11)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f251,f129])).
% 1.33/0.55  fof(f129,plain,(
% 1.33/0.55    v1_funct_2(sK11,k1_tarski(sK9),sK10)),
% 1.33/0.55    inference(cnf_transformation,[],[f86])).
% 1.33/0.55  fof(f251,plain,(
% 1.33/0.55    ( ! [X2] : (r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11)) | ~r2_hidden(X2,k1_tarski(sK9)) | ~v1_funct_2(sK11,k1_tarski(sK9),sK10) | ~v1_funct_1(sK11)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f241,f131])).
% 1.33/0.55  fof(f241,plain,(
% 1.33/0.55    ( ! [X2] : (r2_hidden(k1_funct_1(sK11,X2),k2_relset_1(k1_tarski(sK9),sK10,sK11)) | k1_xboole_0 = sK10 | ~r2_hidden(X2,k1_tarski(sK9)) | ~v1_funct_2(sK11,k1_tarski(sK9),sK10) | ~v1_funct_1(sK11)) )),
% 1.33/0.55    inference(resolution,[],[f130,f202])).
% 1.33/0.55  fof(f202,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f69])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.33/0.55    inference(flattening,[],[f68])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.33/0.55    inference(ennf_transformation,[],[f32])).
% 1.33/0.55  fof(f32,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (29439)------------------------------
% 1.33/0.55  % (29439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (29439)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (29439)Memory used [KB]: 2046
% 1.33/0.55  % (29439)Time elapsed: 0.123 s
% 1.33/0.55  % (29439)------------------------------
% 1.33/0.55  % (29439)------------------------------
% 1.33/0.55  % (29430)Success in time 0.189 s
%------------------------------------------------------------------------------
