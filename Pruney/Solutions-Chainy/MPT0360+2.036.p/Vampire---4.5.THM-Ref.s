%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:53 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 655 expanded)
%              Number of leaves         :   23 ( 178 expanded)
%              Depth                    :   25
%              Number of atoms          :  185 (1424 expanded)
%              Number of equality atoms :   54 ( 419 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1893,plain,(
    $false ),
    inference(global_subsumption,[],[f1110,f1877])).

fof(f1877,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f1113,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1113,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f994,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f89,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f994,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f756,f766,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f766,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f749,f129])).

fof(f129,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f749,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f56,f715,f345])).

fof(f345,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,sK2)
      | r1_tarski(X12,sK0)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f102,f207])).

fof(f207,plain,
    ( r1_tarski(sK2,sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f204,f149])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f81,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f204,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f199,f128])).

fof(f128,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f199,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f715,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f698,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f60,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f698,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f56,f688,f102])).

fof(f688,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f60,f639,f102])).

fof(f639,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f590,f120])).

fof(f590,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f160,f573,f82])).

fof(f573,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f411,f382])).

fof(f382,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f305,f139])).

fof(f305,plain,(
    ! [X10] :
      ( ~ r1_tarski(k1_zfmisc_1(sK2),X10)
      | r2_hidden(sK1,X10) ) ),
    inference(resolution,[],[f92,f160])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f411,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(backward_demodulation,[],[f132,f400])).

fof(f400,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f101,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f101,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f132,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) ),
    inference(forward_demodulation,[],[f130,f101])).

fof(f130,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ) ),
    inference(definition_unfolding,[],[f104,f117,f118])).

fof(f118,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f114])).

fof(f114,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f77,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f100,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f106,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f107,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f108,f109])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f117,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f78,f116])).

fof(f116,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f79,f115])).

fof(f115,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f114])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f160,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f56,f129])).

fof(f56,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f756,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f715,f81])).

fof(f58,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1110,plain,(
    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f56,f55,f994,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:40:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (7015)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (6999)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (7003)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (7004)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (7007)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (7001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (7028)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (7020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (6998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (7022)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (7019)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (7013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (7012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (7002)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (7011)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (7023)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (7017)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (7014)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (7005)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (7002)Refutation not found, incomplete strategy% (7002)------------------------------
% 0.20/0.54  % (7002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7002)Memory used [KB]: 6396
% 0.20/0.54  % (7002)Time elapsed: 0.129 s
% 0.20/0.54  % (7002)------------------------------
% 0.20/0.54  % (7002)------------------------------
% 0.20/0.54  % (7018)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (7024)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (7027)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (7010)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (7026)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (7020)Refutation not found, incomplete strategy% (7020)------------------------------
% 0.20/0.55  % (7020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7009)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (7025)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (7020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7020)Memory used [KB]: 10746
% 0.20/0.55  % (7020)Time elapsed: 0.144 s
% 0.20/0.55  % (7020)------------------------------
% 0.20/0.55  % (7020)------------------------------
% 0.20/0.56  % (7006)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (7000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (7016)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (7008)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.10/0.70  % (7023)Refutation found. Thanks to Tanya!
% 2.10/0.70  % SZS status Theorem for theBenchmark
% 2.10/0.70  % SZS output start Proof for theBenchmark
% 2.10/0.71  fof(f1893,plain,(
% 2.10/0.71    $false),
% 2.10/0.71    inference(global_subsumption,[],[f1110,f1877])).
% 2.10/0.71  fof(f1877,plain,(
% 2.10/0.71    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f57,f1113,f102])).
% 2.10/0.71  fof(f102,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f54])).
% 2.10/0.71  fof(f54,plain,(
% 2.10/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.10/0.71    inference(flattening,[],[f53])).
% 2.10/0.71  fof(f53,plain,(
% 2.10/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.10/0.71    inference(ennf_transformation,[],[f6])).
% 2.10/0.71  fof(f6,axiom,(
% 2.10/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.10/0.71  fof(f1113,plain,(
% 2.10/0.71    ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f58,f994,f120])).
% 2.10/0.71  fof(f120,plain,(
% 2.10/0.71    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.71    inference(definition_unfolding,[],[f89,f61])).
% 2.10/0.71  fof(f61,plain,(
% 2.10/0.71    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f30])).
% 2.10/0.71  fof(f30,axiom,(
% 2.10/0.71    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 2.10/0.71  fof(f89,plain,(
% 2.10/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 2.10/0.71    inference(cnf_transformation,[],[f49])).
% 2.10/0.71  fof(f49,plain,(
% 2.10/0.71    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.71    inference(ennf_transformation,[],[f34])).
% 2.10/0.71  fof(f34,axiom,(
% 2.10/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 2.10/0.71  fof(f994,plain,(
% 2.10/0.71    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f756,f766,f82])).
% 2.10/0.71  fof(f82,plain,(
% 2.10/0.71    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f43])).
% 2.10/0.71  fof(f43,plain,(
% 2.10/0.71    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.10/0.71    inference(ennf_transformation,[],[f29])).
% 2.10/0.71  fof(f29,axiom,(
% 2.10/0.71    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.10/0.71  fof(f766,plain,(
% 2.10/0.71    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f749,f129])).
% 2.10/0.71  fof(f129,plain,(
% 2.10/0.71    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.10/0.71    inference(equality_resolution,[],[f95])).
% 2.10/0.71  fof(f95,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.10/0.71    inference(cnf_transformation,[],[f22])).
% 2.10/0.71  fof(f22,axiom,(
% 2.10/0.71    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.10/0.71  fof(f749,plain,(
% 2.10/0.71    r1_tarski(sK1,sK0)),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f56,f715,f345])).
% 2.10/0.71  fof(f345,plain,(
% 2.10/0.71    ( ! [X12] : (~r1_tarski(X12,sK2) | r1_tarski(X12,sK0) | v1_xboole_0(sK2)) )),
% 2.10/0.71    inference(resolution,[],[f102,f207])).
% 2.10/0.71  fof(f207,plain,(
% 2.10/0.71    r1_tarski(sK2,sK0) | v1_xboole_0(sK2)),
% 2.10/0.71    inference(resolution,[],[f204,f149])).
% 2.10/0.71  fof(f149,plain,(
% 2.10/0.71    ~v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(sK2)),
% 2.10/0.71    inference(resolution,[],[f81,f55])).
% 2.10/0.71  fof(f55,plain,(
% 2.10/0.71    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.10/0.71    inference(cnf_transformation,[],[f39])).
% 2.10/0.71  fof(f39,plain,(
% 2.10/0.71    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.10/0.71    inference(flattening,[],[f38])).
% 2.10/0.71  fof(f38,plain,(
% 2.10/0.71    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.10/0.71    inference(ennf_transformation,[],[f36])).
% 2.10/0.71  fof(f36,negated_conjecture,(
% 2.10/0.71    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.10/0.71    inference(negated_conjecture,[],[f35])).
% 2.10/0.71  fof(f35,conjecture,(
% 2.10/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 2.10/0.71  fof(f81,plain,(
% 2.10/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f43])).
% 2.10/0.71  fof(f204,plain,(
% 2.10/0.71    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK0)),
% 2.10/0.71    inference(resolution,[],[f199,f128])).
% 2.10/0.71  fof(f128,plain,(
% 2.10/0.71    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.10/0.71    inference(equality_resolution,[],[f96])).
% 2.10/0.71  fof(f96,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.10/0.71    inference(cnf_transformation,[],[f22])).
% 2.10/0.71  fof(f199,plain,(
% 2.10/0.71    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.10/0.71    inference(resolution,[],[f83,f55])).
% 2.10/0.71  fof(f83,plain,(
% 2.10/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f43])).
% 2.10/0.71  fof(f715,plain,(
% 2.10/0.71    ~v1_xboole_0(sK2)),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f698,f139])).
% 2.10/0.71  fof(f139,plain,(
% 2.10/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.10/0.71    inference(superposition,[],[f60,f68])).
% 2.10/0.71  fof(f68,plain,(
% 2.10/0.71    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f41])).
% 2.10/0.71  fof(f41,plain,(
% 2.10/0.71    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.10/0.71    inference(ennf_transformation,[],[f3])).
% 2.10/0.71  fof(f3,axiom,(
% 2.10/0.71    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.10/0.71  fof(f60,plain,(
% 2.10/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f7])).
% 2.10/0.71  fof(f7,axiom,(
% 2.10/0.71    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.10/0.71  fof(f698,plain,(
% 2.10/0.71    ~r1_tarski(sK2,k1_xboole_0)),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f56,f688,f102])).
% 2.10/0.71  fof(f688,plain,(
% 2.10/0.71    ~r1_tarski(sK1,k1_xboole_0)),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f60,f639,f102])).
% 2.10/0.71  fof(f639,plain,(
% 2.10/0.71    ~r1_tarski(sK1,k3_subset_1(sK2,sK1))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f58,f590,f120])).
% 2.10/0.71  fof(f590,plain,(
% 2.10/0.71    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f160,f573,f82])).
% 2.10/0.71  fof(f573,plain,(
% 2.10/0.71    ~v1_xboole_0(k1_zfmisc_1(sK2))),
% 2.10/0.71    inference(unit_resulting_resolution,[],[f411,f382])).
% 2.10/0.71  fof(f382,plain,(
% 2.10/0.71    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(sK2)) | r2_hidden(sK1,X0)) )),
% 2.10/0.71    inference(resolution,[],[f305,f139])).
% 2.10/0.71  fof(f305,plain,(
% 2.10/0.71    ( ! [X10] : (~r1_tarski(k1_zfmisc_1(sK2),X10) | r2_hidden(sK1,X10)) )),
% 2.10/0.71    inference(resolution,[],[f92,f160])).
% 2.10/0.71  fof(f92,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f51])).
% 2.10/0.71  fof(f51,plain,(
% 2.10/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.10/0.71    inference(ennf_transformation,[],[f1])).
% 2.10/0.71  fof(f1,axiom,(
% 2.10/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.10/0.71  fof(f411,plain,(
% 2.10/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 2.10/0.71    inference(backward_demodulation,[],[f132,f400])).
% 2.10/0.71  fof(f400,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.10/0.71    inference(superposition,[],[f101,f62])).
% 2.10/0.71  fof(f62,plain,(
% 2.10/0.71    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f13])).
% 2.10/0.71  fof(f13,axiom,(
% 2.10/0.71    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.10/0.71  fof(f101,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.10/0.71    inference(cnf_transformation,[],[f12])).
% 2.10/0.71  fof(f12,axiom,(
% 2.10/0.71    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.10/0.71  fof(f132,plain,(
% 2.10/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))))) )),
% 2.10/0.71    inference(forward_demodulation,[],[f130,f101])).
% 2.10/0.71  fof(f130,plain,(
% 2.10/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 2.10/0.71    inference(equality_resolution,[],[f123])).
% 2.10/0.71  fof(f123,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 2.10/0.71    inference(definition_unfolding,[],[f104,f117,f118])).
% 2.10/0.71  fof(f118,plain,(
% 2.10/0.71    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.10/0.71    inference(definition_unfolding,[],[f65,f114])).
% 2.10/0.71  fof(f114,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.10/0.71    inference(definition_unfolding,[],[f77,f113])).
% 2.10/0.71  fof(f113,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.10/0.71    inference(definition_unfolding,[],[f100,f112])).
% 2.10/0.71  fof(f112,plain,(
% 2.10/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.10/0.71    inference(definition_unfolding,[],[f106,f111])).
% 2.10/0.71  fof(f111,plain,(
% 2.10/0.71    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.10/0.71    inference(definition_unfolding,[],[f107,f110])).
% 2.10/0.71  fof(f110,plain,(
% 2.10/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.10/0.71    inference(definition_unfolding,[],[f108,f109])).
% 2.10/0.71  fof(f109,plain,(
% 2.10/0.71    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f21])).
% 2.10/0.71  fof(f21,axiom,(
% 2.10/0.71    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.10/0.71  fof(f108,plain,(
% 2.10/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f20])).
% 2.10/0.71  fof(f20,axiom,(
% 2.10/0.71    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.10/0.71  fof(f107,plain,(
% 2.10/0.71    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f19])).
% 2.10/0.71  fof(f19,axiom,(
% 2.10/0.71    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.10/0.71  fof(f106,plain,(
% 2.10/0.71    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f18])).
% 2.10/0.71  fof(f18,axiom,(
% 2.10/0.71    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.10/0.71  fof(f100,plain,(
% 2.10/0.71    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f17])).
% 2.10/0.71  fof(f17,axiom,(
% 2.10/0.71    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.10/0.71  fof(f77,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f16])).
% 2.10/0.71  fof(f16,axiom,(
% 2.10/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.10/0.71  fof(f65,plain,(
% 2.10/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.10/0.71    inference(cnf_transformation,[],[f15])).
% 2.10/0.71  fof(f15,axiom,(
% 2.10/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.10/0.71  fof(f117,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.10/0.71    inference(definition_unfolding,[],[f78,f116])).
% 2.10/0.71  fof(f116,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.10/0.71    inference(definition_unfolding,[],[f79,f115])).
% 2.10/0.71  fof(f115,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.10/0.71    inference(definition_unfolding,[],[f76,f114])).
% 2.10/0.71  fof(f76,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.10/0.71    inference(cnf_transformation,[],[f24])).
% 2.10/0.71  fof(f24,axiom,(
% 2.10/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.10/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.10/0.71  fof(f79,plain,(
% 2.10/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.10/0.71    inference(cnf_transformation,[],[f14])).
% 2.68/0.71  fof(f14,axiom,(
% 2.68/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.68/0.71  fof(f78,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f5])).
% 2.68/0.71  fof(f5,axiom,(
% 2.68/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.68/0.71  fof(f104,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f27])).
% 2.68/0.71  fof(f27,axiom,(
% 2.68/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.68/0.71  fof(f160,plain,(
% 2.68/0.71    r2_hidden(sK1,k1_zfmisc_1(sK2))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f56,f129])).
% 2.68/0.71  fof(f56,plain,(
% 2.68/0.71    r1_tarski(sK1,sK2)),
% 2.68/0.71    inference(cnf_transformation,[],[f39])).
% 2.68/0.71  fof(f756,plain,(
% 2.68/0.71    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f55,f715,f81])).
% 2.68/0.71  fof(f58,plain,(
% 2.68/0.71    k1_xboole_0 != sK1),
% 2.68/0.71    inference(cnf_transformation,[],[f39])).
% 2.68/0.71  fof(f57,plain,(
% 2.68/0.71    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.68/0.71    inference(cnf_transformation,[],[f39])).
% 2.68/0.71  fof(f1110,plain,(
% 2.68/0.71    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f56,f55,f994,f91])).
% 2.68/0.71  fof(f91,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f50])).
% 2.68/0.71  fof(f50,plain,(
% 2.68/0.71    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f33])).
% 2.68/0.71  fof(f33,axiom,(
% 2.68/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 2.68/0.71  % SZS output end Proof for theBenchmark
% 2.68/0.71  % (7023)------------------------------
% 2.68/0.71  % (7023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.71  % (7023)Termination reason: Refutation
% 2.68/0.71  
% 2.68/0.71  % (7023)Memory used [KB]: 8315
% 2.68/0.71  % (7023)Time elapsed: 0.283 s
% 2.68/0.71  % (7023)------------------------------
% 2.68/0.71  % (7023)------------------------------
% 2.68/0.72  % (6997)Success in time 0.354 s
%------------------------------------------------------------------------------
