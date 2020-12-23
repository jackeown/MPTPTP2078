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
% DateTime   : Thu Dec  3 12:44:53 EST 2020

% Result     : Theorem 2.68s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 533 expanded)
%              Number of leaves         :   26 ( 149 expanded)
%              Depth                    :   22
%              Number of atoms          :  202 (1080 expanded)
%              Number of equality atoms :   61 ( 355 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2334,plain,(
    $false ),
    inference(global_subsumption,[],[f1410,f2325])).

fof(f2325,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f1404,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1404,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f59,f1181,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f90,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f1181,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1009,f1033,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1033,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1000,f139])).

fof(f139,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
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

fof(f1000,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f57,f994,f464])).

fof(f464,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,sK2)
      | r1_tarski(X12,sK0)
      | v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f110,f229])).

fof(f229,plain,
    ( r1_tarski(sK2,sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f226,f159])).

fof(f159,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f226,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f221,f138])).

fof(f138,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f221,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f994,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f957,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f61,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f957,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f779,f375])).

fof(f375,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1),X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f347,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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

fof(f347,plain,(
    r2_hidden(sK3(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f57,f158,f93])).

fof(f158,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f779,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f61,f538,f93])).

fof(f538,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(backward_demodulation,[],[f142,f527])).

fof(f527,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f109,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f109,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f142,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) ),
    inference(forward_demodulation,[],[f140,f109])).

fof(f140,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ) ),
    inference(definition_unfolding,[],[f112,f125,f126])).

fof(f126,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f122])).

fof(f122,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f108,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f114,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f115,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f116,f117])).

fof(f117,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f114,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f108,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f125,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f79,f124])).

fof(f124,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f80,f123])).

fof(f123,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f122])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f112,plain,(
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

fof(f1009,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f56,f994,f82])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f1410,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1398,f513])).

fof(f513,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f56,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1398,plain,(
    r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f480,f1181,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f480,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f56,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f58,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:54:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (32607)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (32598)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (32590)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (32586)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (32587)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (32589)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (32592)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.53  % (32584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (32612)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (32583)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (32611)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (32591)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (32593)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (32588)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (32597)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (32600)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (32604)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (32610)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (32588)Refutation not found, incomplete strategy% (32588)------------------------------
% 0.19/0.53  % (32588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (32588)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (32588)Memory used [KB]: 6396
% 0.19/0.53  % (32588)Time elapsed: 0.124 s
% 0.19/0.53  % (32588)------------------------------
% 0.19/0.53  % (32588)------------------------------
% 0.19/0.54  % (32603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (32595)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (32605)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (32609)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.54  % (32608)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (32613)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (32596)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (32594)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.55  % (32602)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.55  % (32601)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.55  % (32599)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.55  % (32606)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.56  % (32606)Refutation not found, incomplete strategy% (32606)------------------------------
% 0.19/0.56  % (32606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (32606)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (32606)Memory used [KB]: 10746
% 0.19/0.56  % (32606)Time elapsed: 0.159 s
% 0.19/0.56  % (32606)------------------------------
% 0.19/0.56  % (32606)------------------------------
% 2.12/0.69  % (32671)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.70  % (32670)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.68/0.71  % (32608)Refutation found. Thanks to Tanya!
% 2.68/0.71  % SZS status Theorem for theBenchmark
% 2.68/0.71  % SZS output start Proof for theBenchmark
% 2.68/0.71  fof(f2334,plain,(
% 2.68/0.71    $false),
% 2.68/0.71    inference(global_subsumption,[],[f1410,f2325])).
% 2.68/0.71  fof(f2325,plain,(
% 2.68/0.71    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f57,f1404,f110])).
% 2.68/0.71  fof(f110,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f55])).
% 2.68/0.71  fof(f55,plain,(
% 2.68/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.68/0.71    inference(flattening,[],[f54])).
% 2.68/0.71  fof(f54,plain,(
% 2.68/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.68/0.71    inference(ennf_transformation,[],[f5])).
% 2.68/0.71  fof(f5,axiom,(
% 2.68/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.68/0.71  fof(f1404,plain,(
% 2.68/0.71    ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f59,f1181,f128])).
% 2.68/0.71  fof(f128,plain,(
% 2.68/0.71    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.71    inference(definition_unfolding,[],[f90,f62])).
% 2.68/0.71  fof(f62,plain,(
% 2.68/0.71    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f31])).
% 2.68/0.71  fof(f31,axiom,(
% 2.68/0.71    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 2.68/0.71  fof(f90,plain,(
% 2.68/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f50])).
% 2.68/0.71  fof(f50,plain,(
% 2.68/0.71    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f35])).
% 2.68/0.71  fof(f35,axiom,(
% 2.68/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 2.68/0.71  fof(f1181,plain,(
% 2.68/0.71    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f1009,f1033,f83])).
% 2.68/0.71  fof(f83,plain,(
% 2.68/0.71    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f44])).
% 2.68/0.71  fof(f44,plain,(
% 2.68/0.71    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f30])).
% 2.68/0.71  fof(f30,axiom,(
% 2.68/0.71    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.68/0.71  fof(f1033,plain,(
% 2.68/0.71    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f1000,f139])).
% 2.68/0.71  fof(f139,plain,(
% 2.68/0.71    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.68/0.71    inference(equality_resolution,[],[f103])).
% 2.68/0.71  fof(f103,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.68/0.71    inference(cnf_transformation,[],[f22])).
% 2.68/0.71  fof(f22,axiom,(
% 2.68/0.71    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.68/0.71  fof(f1000,plain,(
% 2.68/0.71    r1_tarski(sK1,sK0)),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f57,f994,f464])).
% 2.68/0.71  fof(f464,plain,(
% 2.68/0.71    ( ! [X12] : (~r1_tarski(X12,sK2) | r1_tarski(X12,sK0) | v1_xboole_0(sK2)) )),
% 2.68/0.71    inference(resolution,[],[f110,f229])).
% 2.68/0.71  fof(f229,plain,(
% 2.68/0.71    r1_tarski(sK2,sK0) | v1_xboole_0(sK2)),
% 2.68/0.71    inference(resolution,[],[f226,f159])).
% 2.68/0.71  fof(f159,plain,(
% 2.68/0.71    ~v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(sK2)),
% 2.68/0.71    inference(resolution,[],[f82,f56])).
% 2.68/0.71  fof(f56,plain,(
% 2.68/0.71    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(cnf_transformation,[],[f40])).
% 2.68/0.71  fof(f40,plain,(
% 2.68/0.71    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(flattening,[],[f39])).
% 2.68/0.71  fof(f39,plain,(
% 2.68/0.71    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f37])).
% 2.68/0.71  fof(f37,negated_conjecture,(
% 2.68/0.71    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.68/0.71    inference(negated_conjecture,[],[f36])).
% 2.68/0.71  fof(f36,conjecture,(
% 2.68/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 2.68/0.71  fof(f82,plain,(
% 2.68/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f44])).
% 2.68/0.71  fof(f226,plain,(
% 2.68/0.71    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK0)),
% 2.68/0.71    inference(resolution,[],[f221,f138])).
% 2.68/0.71  fof(f138,plain,(
% 2.68/0.71    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.68/0.71    inference(equality_resolution,[],[f104])).
% 2.68/0.71  fof(f104,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.68/0.71    inference(cnf_transformation,[],[f22])).
% 2.68/0.71  fof(f221,plain,(
% 2.68/0.71    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(resolution,[],[f84,f56])).
% 2.68/0.71  fof(f84,plain,(
% 2.68/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f44])).
% 2.68/0.71  fof(f994,plain,(
% 2.68/0.71    ~v1_xboole_0(sK2)),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f957,f149])).
% 2.68/0.71  fof(f149,plain,(
% 2.68/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.68/0.71    inference(superposition,[],[f61,f69])).
% 2.68/0.71  fof(f69,plain,(
% 2.68/0.71    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f42])).
% 2.68/0.71  fof(f42,plain,(
% 2.68/0.71    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.68/0.71    inference(ennf_transformation,[],[f10])).
% 2.68/0.71  fof(f10,axiom,(
% 2.68/0.71    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 2.68/0.71  fof(f61,plain,(
% 2.68/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f6])).
% 2.68/0.71  fof(f6,axiom,(
% 2.68/0.71    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.68/0.71  fof(f957,plain,(
% 2.68/0.71    ~r1_tarski(sK2,k1_xboole_0)),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f779,f375])).
% 2.68/0.71  fof(f375,plain,(
% 2.68/0.71    ( ! [X0] : (r2_hidden(sK3(sK1),X0) | ~r1_tarski(sK2,X0)) )),
% 2.68/0.71    inference(resolution,[],[f347,f93])).
% 2.68/0.71  fof(f93,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f52])).
% 2.68/0.71  fof(f52,plain,(
% 2.68/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f1])).
% 2.68/0.71  fof(f1,axiom,(
% 2.68/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.68/0.71  fof(f347,plain,(
% 2.68/0.71    r2_hidden(sK3(sK1),sK2)),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f57,f158,f93])).
% 2.68/0.71  fof(f158,plain,(
% 2.68/0.71    r2_hidden(sK3(sK1),sK1)),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f59,f70])).
% 2.68/0.71  fof(f70,plain,(
% 2.68/0.71    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.68/0.71    inference(cnf_transformation,[],[f43])).
% 2.68/0.71  fof(f43,plain,(
% 2.68/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.68/0.71    inference(ennf_transformation,[],[f3])).
% 2.68/0.71  fof(f3,axiom,(
% 2.68/0.71    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.68/0.71  fof(f779,plain,(
% 2.68/0.71    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f61,f538,f93])).
% 2.68/0.71  fof(f538,plain,(
% 2.68/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 2.68/0.71    inference(backward_demodulation,[],[f142,f527])).
% 2.68/0.71  fof(f527,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.68/0.71    inference(superposition,[],[f109,f63])).
% 2.68/0.71  fof(f63,plain,(
% 2.68/0.71    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f13])).
% 2.68/0.71  fof(f13,axiom,(
% 2.68/0.71    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.68/0.71  fof(f109,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f12])).
% 2.68/0.71  fof(f12,axiom,(
% 2.68/0.71    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.68/0.71  fof(f142,plain,(
% 2.68/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))))) )),
% 2.68/0.71    inference(forward_demodulation,[],[f140,f109])).
% 2.68/0.71  fof(f140,plain,(
% 2.68/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 2.68/0.71    inference(equality_resolution,[],[f131])).
% 2.68/0.71  fof(f131,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 2.68/0.71    inference(definition_unfolding,[],[f112,f125,f126])).
% 2.68/0.71  fof(f126,plain,(
% 2.68/0.71    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.68/0.71    inference(definition_unfolding,[],[f66,f122])).
% 2.68/0.71  fof(f122,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.68/0.71    inference(definition_unfolding,[],[f78,f121])).
% 2.68/0.71  fof(f121,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.68/0.71    inference(definition_unfolding,[],[f108,f120])).
% 2.68/0.71  fof(f120,plain,(
% 2.68/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.68/0.71    inference(definition_unfolding,[],[f114,f119])).
% 2.68/0.71  fof(f119,plain,(
% 2.68/0.71    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.68/0.71    inference(definition_unfolding,[],[f115,f118])).
% 2.68/0.71  fof(f118,plain,(
% 2.68/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.68/0.71    inference(definition_unfolding,[],[f116,f117])).
% 2.68/0.71  fof(f117,plain,(
% 2.68/0.71    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f21])).
% 2.68/0.71  fof(f21,axiom,(
% 2.68/0.71    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.68/0.71  fof(f116,plain,(
% 2.68/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f20])).
% 2.68/0.71  fof(f20,axiom,(
% 2.68/0.71    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.68/0.71  fof(f115,plain,(
% 2.68/0.71    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f19])).
% 2.68/0.71  fof(f19,axiom,(
% 2.68/0.71    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.68/0.71  fof(f114,plain,(
% 2.68/0.71    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f18])).
% 2.68/0.71  fof(f18,axiom,(
% 2.68/0.71    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.68/0.71  fof(f108,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f17])).
% 2.68/0.71  fof(f17,axiom,(
% 2.68/0.71    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.68/0.71  fof(f78,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f16])).
% 2.68/0.71  fof(f16,axiom,(
% 2.68/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.68/0.71  fof(f66,plain,(
% 2.68/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f15])).
% 2.68/0.71  fof(f15,axiom,(
% 2.68/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.68/0.71  fof(f125,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.68/0.71    inference(definition_unfolding,[],[f79,f124])).
% 2.68/0.71  fof(f124,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.68/0.71    inference(definition_unfolding,[],[f80,f123])).
% 2.68/0.71  fof(f123,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.68/0.71    inference(definition_unfolding,[],[f77,f122])).
% 2.68/0.71  fof(f77,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f24])).
% 2.68/0.71  fof(f24,axiom,(
% 2.68/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.68/0.71  fof(f80,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f14])).
% 2.68/0.71  fof(f14,axiom,(
% 2.68/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.68/0.71  fof(f79,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f4])).
% 2.68/0.71  fof(f4,axiom,(
% 2.68/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.68/0.71  fof(f112,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f27])).
% 2.68/0.71  fof(f27,axiom,(
% 2.68/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.68/0.71  fof(f1009,plain,(
% 2.68/0.71    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f56,f994,f82])).
% 2.68/0.71  fof(f59,plain,(
% 2.68/0.71    k1_xboole_0 != sK1),
% 2.68/0.71    inference(cnf_transformation,[],[f40])).
% 2.68/0.71  fof(f57,plain,(
% 2.68/0.71    r1_tarski(sK1,sK2)),
% 2.68/0.71    inference(cnf_transformation,[],[f40])).
% 2.68/0.71  fof(f1410,plain,(
% 2.68/0.71    r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 2.68/0.71    inference(forward_demodulation,[],[f1398,f513])).
% 2.68/0.71  fof(f513,plain,(
% 2.68/0.71    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f56,f88])).
% 2.68/0.71  fof(f88,plain,(
% 2.68/0.71    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f49])).
% 2.68/0.71  fof(f49,plain,(
% 2.68/0.71    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f33])).
% 2.68/0.71  fof(f33,axiom,(
% 2.68/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.68/0.71  fof(f1398,plain,(
% 2.68/0.71    r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f58,f480,f1181,f92])).
% 2.68/0.71  fof(f92,plain,(
% 2.68/0.71    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2)) )),
% 2.68/0.71    inference(cnf_transformation,[],[f51])).
% 2.68/0.71  fof(f51,plain,(
% 2.68/0.71    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f34])).
% 2.68/0.71  fof(f34,axiom,(
% 2.68/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 2.68/0.71  fof(f480,plain,(
% 2.68/0.71    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 2.68/0.71    inference(unit_resulting_resolution,[],[f56,f87])).
% 2.68/0.71  fof(f87,plain,(
% 2.68/0.71    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/0.71    inference(cnf_transformation,[],[f48])).
% 2.68/0.71  fof(f48,plain,(
% 2.68/0.71    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/0.71    inference(ennf_transformation,[],[f32])).
% 2.68/0.71  fof(f32,axiom,(
% 2.68/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.68/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.68/0.71  fof(f58,plain,(
% 2.68/0.71    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.68/0.71    inference(cnf_transformation,[],[f40])).
% 2.68/0.71  % SZS output end Proof for theBenchmark
% 2.68/0.71  % (32608)------------------------------
% 2.68/0.71  % (32608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.71  % (32608)Termination reason: Refutation
% 2.68/0.71  
% 2.68/0.71  % (32608)Memory used [KB]: 8699
% 2.68/0.71  % (32608)Time elapsed: 0.312 s
% 2.68/0.71  % (32608)------------------------------
% 2.68/0.71  % (32608)------------------------------
% 2.68/0.71  % (32577)Success in time 0.359 s
%------------------------------------------------------------------------------
