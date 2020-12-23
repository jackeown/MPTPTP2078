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
% DateTime   : Thu Dec  3 13:04:10 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  101 (1827 expanded)
%              Number of leaves         :   18 ( 535 expanded)
%              Depth                    :   28
%              Number of atoms          :  284 (3897 expanded)
%              Number of equality atoms :  151 (2247 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(subsumption_resolution,[],[f384,f215])).

fof(f215,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(backward_demodulation,[],[f88,f213])).

fof(f213,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f211,f130])).

fof(f130,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f127,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X0,X0,X1,X2) = X3
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f76,f86,f86,f86,f85,f85,f85,f61,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f85])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X3
      | k1_tarski(X0) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X2) = X3
      | k2_tarski(X0,X1) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k1_enumset1(X0,X1,X2) = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f127,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f126,f88])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(resolution,[],[f122,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f122,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK2,X1)
      | r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(resolution,[],[f119,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f119,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f211,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(equality_factoring,[],[f184])).

fof(f184,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f179,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f149,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f149,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f148,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f148,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f143,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f126,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f123,f130])).

fof(f123,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f179,plain,(
    ! [X2] :
      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X2)
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ) ),
    inference(resolution,[],[f173,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f172,f149])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(X0,sK5(k1_xboole_0,X0)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f170,f133])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k4_tarski(X0,sK5(sK2,X0)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f169,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f168,f88])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) ) ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) ) ),
    inference(superposition,[],[f74,f163])).

fof(f163,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f117,f88])).

fof(f117,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(resolution,[],[f89,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f89,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f86])).

fof(f40,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f41,f86])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f384,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(superposition,[],[f360,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f360,plain,(
    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(backward_demodulation,[],[f214,f359])).

fof(f359,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f356,f213])).

fof(f356,plain,(
    ! [X0] :
      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f119])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    inference(resolution,[],[f39,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f53,f86,f86])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f214,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(backward_demodulation,[],[f87,f213])).

fof(f87,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f43,f86,f86])).

fof(f43,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.30/0.54  % (7144)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (7139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.57  % (7145)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.57  % (7145)Refutation not found, incomplete strategy% (7145)------------------------------
% 1.50/0.57  % (7145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (7145)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (7145)Memory used [KB]: 10618
% 1.50/0.57  % (7145)Time elapsed: 0.140 s
% 1.50/0.57  % (7145)------------------------------
% 1.50/0.57  % (7145)------------------------------
% 1.50/0.57  % (7138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.57  % (7136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.58  % (7147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.58  % (7160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.58  % (7141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.58  % (7155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.59  % (7137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.59  % (7159)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.59  % (7140)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.60  % (7149)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.60  % (7155)Refutation not found, incomplete strategy% (7155)------------------------------
% 1.50/0.60  % (7155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (7155)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  % (7142)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.60  
% 1.50/0.60  % (7155)Memory used [KB]: 10874
% 1.50/0.60  % (7155)Time elapsed: 0.165 s
% 1.50/0.60  % (7155)------------------------------
% 1.50/0.60  % (7155)------------------------------
% 1.50/0.60  % (7135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.61  % (7135)Refutation not found, incomplete strategy% (7135)------------------------------
% 1.50/0.61  % (7135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (7135)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.61  
% 1.50/0.61  % (7135)Memory used [KB]: 1791
% 1.50/0.61  % (7135)Time elapsed: 0.178 s
% 1.50/0.61  % (7135)------------------------------
% 1.50/0.61  % (7135)------------------------------
% 1.50/0.61  % (7163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.61  % (7150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.61  % (7148)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.61  % (7164)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.61  % (7161)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.61  % (7143)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.61  % (7158)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.61  % (7146)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.61  % (7156)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.62  % (7157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.62  % (7154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.62  % (7157)Refutation not found, incomplete strategy% (7157)------------------------------
% 1.50/0.62  % (7157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (7157)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.62  
% 1.50/0.62  % (7157)Memory used [KB]: 10874
% 1.50/0.62  % (7157)Time elapsed: 0.193 s
% 1.50/0.62  % (7157)------------------------------
% 1.50/0.62  % (7157)------------------------------
% 1.50/0.62  % (7151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.62  % (7152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.62  % (7152)Refutation not found, incomplete strategy% (7152)------------------------------
% 1.50/0.62  % (7152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.63  % (7162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.63  % (7153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.63  % (7152)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.63  
% 1.50/0.63  % (7152)Memory used [KB]: 10618
% 1.50/0.63  % (7152)Time elapsed: 0.154 s
% 1.50/0.63  % (7152)------------------------------
% 1.50/0.63  % (7152)------------------------------
% 1.50/0.64  % (7146)Refutation not found, incomplete strategy% (7146)------------------------------
% 1.50/0.64  % (7146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.64  % (7146)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.64  
% 1.50/0.64  % (7146)Memory used [KB]: 10746
% 1.50/0.64  % (7146)Time elapsed: 0.193 s
% 1.50/0.64  % (7146)------------------------------
% 1.50/0.64  % (7146)------------------------------
% 2.13/0.64  % (7156)Refutation found. Thanks to Tanya!
% 2.13/0.64  % SZS status Theorem for theBenchmark
% 2.13/0.64  % SZS output start Proof for theBenchmark
% 2.13/0.64  fof(f385,plain,(
% 2.13/0.64    $false),
% 2.13/0.64    inference(subsumption_resolution,[],[f384,f215])).
% 2.13/0.64  fof(f215,plain,(
% 2.13/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.13/0.64    inference(backward_demodulation,[],[f88,f213])).
% 2.13/0.66  fof(f213,plain,(
% 2.13/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 2.13/0.66    inference(subsumption_resolution,[],[f211,f130])).
% 2.13/0.66  fof(f130,plain,(
% 2.13/0.66    k1_xboole_0 = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 2.13/0.66    inference(duplicate_literal_removal,[],[f128])).
% 2.13/0.66  fof(f128,plain,(
% 2.13/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 2.13/0.66    inference(resolution,[],[f127,f99])).
% 2.13/0.66  fof(f99,plain,(
% 2.13/0.66    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X0) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X0,X0,X1,X2) = X3 | k1_xboole_0 = X3) )),
% 2.13/0.66    inference(definition_unfolding,[],[f76,f86,f86,f86,f85,f85,f85,f61,f61])).
% 2.13/0.66  fof(f61,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f5])).
% 2.13/0.66  fof(f5,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.13/0.66  fof(f85,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.13/0.66    inference(definition_unfolding,[],[f50,f61])).
% 2.13/0.66  fof(f50,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f4])).
% 2.13/0.66  fof(f4,axiom,(
% 2.13/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.13/0.66  fof(f86,plain,(
% 2.13/0.66    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.13/0.66    inference(definition_unfolding,[],[f47,f85])).
% 2.13/0.66  fof(f47,plain,(
% 2.13/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f3])).
% 2.13/0.66  fof(f3,axiom,(
% 2.13/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.13/0.66  fof(f76,plain,(
% 2.13/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X3 | k1_tarski(X0) = X3 | k1_tarski(X1) = X3 | k1_tarski(X2) = X3 | k2_tarski(X0,X1) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k1_enumset1(X0,X1,X2) = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f38])).
% 2.13/0.66  fof(f38,plain,(
% 2.13/0.66    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.13/0.66    inference(ennf_transformation,[],[f6])).
% 2.13/0.66  fof(f6,axiom,(
% 2.13/0.66    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 2.13/0.66  fof(f127,plain,(
% 2.13/0.66    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.13/0.66    inference(resolution,[],[f126,f88])).
% 2.13/0.66  fof(f126,plain,(
% 2.13/0.66    ( ! [X2,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(sK2),X1)) )),
% 2.13/0.66    inference(resolution,[],[f122,f64])).
% 2.13/0.66  fof(f64,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f32])).
% 2.13/0.66  fof(f32,plain,(
% 2.13/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.66    inference(ennf_transformation,[],[f15])).
% 2.13/0.66  fof(f15,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.13/0.66  fof(f122,plain,(
% 2.13/0.66    ( ! [X1] : (~v4_relat_1(sK2,X1) | r1_tarski(k1_relat_1(sK2),X1)) )),
% 2.13/0.66    inference(resolution,[],[f119,f52])).
% 2.13/0.66  fof(f52,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f25])).
% 2.13/0.66  fof(f25,plain,(
% 2.13/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f9])).
% 2.13/0.66  fof(f9,axiom,(
% 2.13/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.13/0.66  fof(f119,plain,(
% 2.13/0.66    v1_relat_1(sK2)),
% 2.13/0.66    inference(resolution,[],[f88,f62])).
% 2.13/0.66  fof(f62,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f30])).
% 2.13/0.66  fof(f30,plain,(
% 2.13/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.66    inference(ennf_transformation,[],[f14])).
% 2.13/0.66  fof(f14,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.13/0.66  fof(f211,plain,(
% 2.13/0.66    k1_xboole_0 != k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 2.13/0.66    inference(equality_factoring,[],[f184])).
% 2.13/0.66  fof(f184,plain,(
% 2.13/0.66    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 2.13/0.66    inference(duplicate_literal_removal,[],[f183])).
% 2.13/0.66  fof(f183,plain,(
% 2.13/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.13/0.66    inference(resolution,[],[f179,f160])).
% 2.13/0.66  fof(f160,plain,(
% 2.13/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = X0) )),
% 2.13/0.66    inference(resolution,[],[f149,f56])).
% 2.13/0.66  fof(f56,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.13/0.66    inference(cnf_transformation,[],[f2])).
% 2.13/0.66  fof(f2,axiom,(
% 2.13/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.13/0.66  fof(f149,plain,(
% 2.13/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)) )),
% 2.13/0.66    inference(forward_demodulation,[],[f148,f44])).
% 2.13/0.66  fof(f44,plain,(
% 2.13/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.13/0.66    inference(cnf_transformation,[],[f10])).
% 2.13/0.66  fof(f10,axiom,(
% 2.13/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.13/0.66  fof(f148,plain,(
% 2.13/0.66    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f143,f46])).
% 2.13/0.66  fof(f46,plain,(
% 2.13/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f7])).
% 2.13/0.66  fof(f7,axiom,(
% 2.13/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.13/0.66  fof(f143,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k1_relat_1(k1_xboole_0),X0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)) )),
% 2.13/0.66    inference(superposition,[],[f126,f133])).
% 2.13/0.66  fof(f133,plain,(
% 2.13/0.66    k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 2.13/0.66    inference(trivial_inequality_removal,[],[f132])).
% 2.13/0.66  fof(f132,plain,(
% 2.13/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 2.13/0.66    inference(superposition,[],[f123,f130])).
% 2.13/0.66  fof(f123,plain,(
% 2.13/0.66    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 2.13/0.66    inference(resolution,[],[f119,f48])).
% 2.13/0.66  fof(f48,plain,(
% 2.13/0.66    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.13/0.66    inference(cnf_transformation,[],[f24])).
% 2.13/0.66  fof(f24,plain,(
% 2.13/0.66    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.13/0.66    inference(flattening,[],[f23])).
% 2.13/0.66  fof(f23,plain,(
% 2.13/0.66    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f11])).
% 2.13/0.66  fof(f11,axiom,(
% 2.13/0.66    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.13/0.66  fof(f179,plain,(
% 2.13/0.66    ( ! [X2] : (r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)) )),
% 2.13/0.66    inference(resolution,[],[f173,f58])).
% 2.13/0.66  fof(f58,plain,(
% 2.13/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f28])).
% 2.13/0.66  fof(f28,plain,(
% 2.13/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f1])).
% 2.13/0.66  fof(f1,axiom,(
% 2.13/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.13/0.66  fof(f173,plain,(
% 2.13/0.66    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f172,f149])).
% 2.13/0.66  fof(f172,plain,(
% 2.13/0.66    ( ! [X0] : (~r1_tarski(k1_xboole_0,k4_tarski(X0,sK5(k1_xboole_0,X0))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)) )),
% 2.13/0.66    inference(superposition,[],[f170,f133])).
% 2.13/0.66  fof(f170,plain,(
% 2.13/0.66    ( ! [X0] : (~r1_tarski(sK2,k4_tarski(X0,sK5(sK2,X0))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 2.13/0.66    inference(resolution,[],[f169,f60])).
% 2.13/0.66  fof(f60,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f29])).
% 2.13/0.66  fof(f29,plain,(
% 2.13/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f13])).
% 2.13/0.66  fof(f13,axiom,(
% 2.13/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.13/0.66  fof(f169,plain,(
% 2.13/0.66    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f168,f88])).
% 2.13/0.66  fof(f168,plain,(
% 2.13/0.66    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)) )),
% 2.13/0.66    inference(trivial_inequality_removal,[],[f165])).
% 2.13/0.66  fof(f165,plain,(
% 2.13/0.66    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k4_tarski(X0,sK5(sK2,X0)),sK2)) )),
% 2.13/0.66    inference(superposition,[],[f74,f163])).
% 2.13/0.66  fof(f163,plain,(
% 2.13/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 2.13/0.66    inference(subsumption_resolution,[],[f117,f88])).
% 2.13/0.66  fof(f117,plain,(
% 2.13/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.13/0.66    inference(subsumption_resolution,[],[f116,f42])).
% 2.13/0.66  fof(f42,plain,(
% 2.13/0.66    k1_xboole_0 != sK1),
% 2.13/0.66    inference(cnf_transformation,[],[f22])).
% 2.13/0.66  fof(f22,plain,(
% 2.13/0.66    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.13/0.66    inference(flattening,[],[f21])).
% 2.13/0.66  fof(f21,plain,(
% 2.13/0.66    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.13/0.66    inference(ennf_transformation,[],[f20])).
% 2.13/0.66  fof(f20,negated_conjecture,(
% 2.13/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 2.13/0.66    inference(negated_conjecture,[],[f19])).
% 2.13/0.66  fof(f19,conjecture,(
% 2.13/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 2.13/0.66  fof(f116,plain,(
% 2.13/0.66    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.13/0.66    inference(resolution,[],[f89,f71])).
% 2.13/0.66  fof(f71,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f34])).
% 2.13/0.66  fof(f34,plain,(
% 2.13/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.66    inference(flattening,[],[f33])).
% 2.13/0.66  fof(f33,plain,(
% 2.13/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.66    inference(ennf_transformation,[],[f18])).
% 2.13/0.66  fof(f18,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.13/0.66  fof(f89,plain,(
% 2.13/0.66    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.13/0.66    inference(definition_unfolding,[],[f40,f86])).
% 2.13/0.66  fof(f40,plain,(
% 2.13/0.66    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 2.13/0.66    inference(cnf_transformation,[],[f22])).
% 2.13/0.66  fof(f74,plain,(
% 2.13/0.66    ( ! [X2,X0,X3,X1] : (k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f35])).
% 2.13/0.66  fof(f35,plain,(
% 2.13/0.66    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.13/0.66    inference(ennf_transformation,[],[f17])).
% 2.13/0.66  fof(f17,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 2.13/0.66  fof(f88,plain,(
% 2.13/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.13/0.66    inference(definition_unfolding,[],[f41,f86])).
% 2.13/0.66  fof(f41,plain,(
% 2.13/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.13/0.66    inference(cnf_transformation,[],[f22])).
% 2.13/0.66  fof(f384,plain,(
% 2.13/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.13/0.66    inference(trivial_inequality_removal,[],[f383])).
% 2.13/0.66  fof(f383,plain,(
% 2.13/0.66    k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.13/0.66    inference(superposition,[],[f360,f63])).
% 2.13/0.66  fof(f63,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f31])).
% 2.13/0.66  fof(f31,plain,(
% 2.13/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.66    inference(ennf_transformation,[],[f16])).
% 2.13/0.66  fof(f16,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.13/0.66  fof(f360,plain,(
% 2.13/0.66    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 2.13/0.66    inference(backward_demodulation,[],[f214,f359])).
% 2.13/0.66  fof(f359,plain,(
% 2.13/0.66    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 2.13/0.66    inference(trivial_inequality_removal,[],[f357])).
% 2.13/0.66  fof(f357,plain,(
% 2.13/0.66    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 2.13/0.66    inference(superposition,[],[f356,f213])).
% 2.13/0.66  fof(f356,plain,(
% 2.13/0.66    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f115,f119])).
% 2.13/0.66  fof(f115,plain,(
% 2.13/0.66    ( ! [X0] : (~v1_relat_1(sK2) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) )),
% 2.13/0.66    inference(resolution,[],[f39,f90])).
% 2.13/0.66  fof(f90,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 2.13/0.66    inference(definition_unfolding,[],[f53,f86,f86])).
% 2.13/0.66  fof(f53,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f27])).
% 2.13/0.66  fof(f27,plain,(
% 2.13/0.66    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.13/0.66    inference(flattening,[],[f26])).
% 2.13/0.66  fof(f26,plain,(
% 2.13/0.66    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.13/0.66    inference(ennf_transformation,[],[f12])).
% 2.13/0.66  fof(f12,axiom,(
% 2.13/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.13/0.66  fof(f39,plain,(
% 2.13/0.66    v1_funct_1(sK2)),
% 2.13/0.66    inference(cnf_transformation,[],[f22])).
% 2.13/0.66  fof(f214,plain,(
% 2.13/0.66    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 2.13/0.66    inference(backward_demodulation,[],[f87,f213])).
% 2.13/0.66  fof(f87,plain,(
% 2.13/0.66    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 2.13/0.66    inference(definition_unfolding,[],[f43,f86,f86])).
% 2.13/0.66  fof(f43,plain,(
% 2.13/0.66    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 2.13/0.66    inference(cnf_transformation,[],[f22])).
% 2.13/0.66  % SZS output end Proof for theBenchmark
% 2.13/0.66  % (7156)------------------------------
% 2.13/0.66  % (7156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (7156)Termination reason: Refutation
% 2.13/0.66  
% 2.13/0.66  % (7156)Memory used [KB]: 1918
% 2.13/0.66  % (7156)Time elapsed: 0.214 s
% 2.13/0.66  % (7156)------------------------------
% 2.13/0.66  % (7156)------------------------------
% 2.13/0.66  % (7134)Success in time 0.298 s
%------------------------------------------------------------------------------
