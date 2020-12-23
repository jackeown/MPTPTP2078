%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:09 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  120 (1564 expanded)
%              Number of leaves         :   19 ( 379 expanded)
%              Depth                    :   31
%              Number of atoms          :  325 (5639 expanded)
%              Number of equality atoms :  112 (2055 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(subsumption_resolution,[],[f403,f176])).

fof(f176,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f154,f56])).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f154,plain,(
    k1_relat_1(k1_xboole_0) != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f117,f139])).

fof(f139,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f99,f128])).

fof(f128,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f122,f127])).

fof(f127,plain,(
    k1_xboole_0 = k11_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f125,f95])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f125,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f124,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f119,f122])).

fof(f119,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f118,f95])).

fof(f118,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f97,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f97,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f55,f94])).

fof(f94,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f53,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f122,plain,(
    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f120,f95])).

fof(f120,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f112,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f112,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f111,f95])).

fof(f111,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f64,f110])).

fof(f110,plain,(
    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f109,f95])).

fof(f109,plain,
    ( sK2 = k7_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f93,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f93,plain,(
    v4_relat_1(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f53,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f99,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f95,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f117,plain,(
    k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f116,f95])).

fof(f116,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f51])).

fof(f115,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f97,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f403,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f393,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f393,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_tarski(sK0))
      | k1_tarski(sK0) = X3 ) ),
    inference(resolution,[],[f389,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f389,plain,(
    ! [X2] : r1_tarski(k1_tarski(sK0),X2) ),
    inference(resolution,[],[f380,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f380,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    inference(resolution,[],[f160,f321])).

fof(f321,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f170,f314])).

fof(f314,plain,(
    ! [X3] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X3) ),
    inference(subsumption_resolution,[],[f306,f58])).

fof(f306,plain,(
    ! [X3] :
      ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X3)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(resolution,[],[f172,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f172,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | k1_xboole_0 = k11_relat_1(k1_xboole_0,X3) ) ),
    inference(forward_demodulation,[],[f171,f139])).

fof(f171,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | k1_xboole_0 = k11_relat_1(sK2,X3) ) ),
    inference(forward_demodulation,[],[f150,f56])).

fof(f150,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 = k11_relat_1(sK2,X3) ) ),
    inference(backward_demodulation,[],[f103,f139])).

fof(f103,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_relat_1(sK2))
      | k1_xboole_0 = k11_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f95,f66])).

fof(f170,plain,(
    ! [X2] :
      ( k1_xboole_0 != k11_relat_1(k1_xboole_0,X2)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f169,f56])).

fof(f169,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 != k11_relat_1(k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f149,f139])).

fof(f149,plain,(
    ! [X2] :
      ( k1_xboole_0 != k11_relat_1(k1_xboole_0,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f102,f139])).

fof(f102,plain,(
    ! [X2] :
      ( k1_xboole_0 != k11_relat_1(sK2,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f160,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f131,f139])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f96,f128])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f90,f51])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f88,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f52,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f52,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (817430528)
% 0.13/0.37  ipcrm: permission denied for id (817463298)
% 0.13/0.37  ipcrm: permission denied for id (817496067)
% 0.13/0.37  ipcrm: permission denied for id (821198852)
% 0.13/0.38  ipcrm: permission denied for id (817561606)
% 0.13/0.38  ipcrm: permission denied for id (817659912)
% 0.13/0.38  ipcrm: permission denied for id (817692681)
% 0.13/0.38  ipcrm: permission denied for id (821329931)
% 0.13/0.38  ipcrm: permission denied for id (817790988)
% 0.13/0.38  ipcrm: permission denied for id (817823757)
% 0.13/0.38  ipcrm: permission denied for id (821362702)
% 0.13/0.39  ipcrm: permission denied for id (821428240)
% 0.13/0.39  ipcrm: permission denied for id (817922065)
% 0.13/0.39  ipcrm: permission denied for id (817954834)
% 0.13/0.39  ipcrm: permission denied for id (821461011)
% 0.21/0.40  ipcrm: permission denied for id (818151447)
% 0.21/0.40  ipcrm: permission denied for id (818184216)
% 0.21/0.40  ipcrm: permission denied for id (818249754)
% 0.21/0.40  ipcrm: permission denied for id (821690397)
% 0.21/0.40  ipcrm: permission denied for id (818348062)
% 0.21/0.41  ipcrm: permission denied for id (821723167)
% 0.21/0.41  ipcrm: permission denied for id (818413600)
% 0.21/0.41  ipcrm: permission denied for id (821755937)
% 0.21/0.41  ipcrm: permission denied for id (818479139)
% 0.21/0.41  ipcrm: permission denied for id (818544677)
% 0.21/0.42  ipcrm: permission denied for id (818577446)
% 0.21/0.42  ipcrm: permission denied for id (818610216)
% 0.21/0.42  ipcrm: permission denied for id (821919786)
% 0.21/0.42  ipcrm: permission denied for id (818675755)
% 0.21/0.42  ipcrm: permission denied for id (818708524)
% 0.21/0.43  ipcrm: permission denied for id (822018095)
% 0.21/0.43  ipcrm: permission denied for id (818839600)
% 0.21/0.43  ipcrm: permission denied for id (818970676)
% 0.21/0.44  ipcrm: permission denied for id (822149173)
% 0.21/0.44  ipcrm: permission denied for id (822181942)
% 0.21/0.44  ipcrm: permission denied for id (819036215)
% 0.21/0.44  ipcrm: permission denied for id (819068984)
% 0.21/0.44  ipcrm: permission denied for id (819101753)
% 0.21/0.44  ipcrm: permission denied for id (822214714)
% 0.21/0.45  ipcrm: permission denied for id (819232829)
% 0.21/0.45  ipcrm: permission denied for id (819298367)
% 0.21/0.45  ipcrm: permission denied for id (822345792)
% 0.21/0.46  ipcrm: permission denied for id (819363905)
% 0.21/0.46  ipcrm: permission denied for id (819396674)
% 0.21/0.46  ipcrm: permission denied for id (819429443)
% 0.21/0.46  ipcrm: permission denied for id (819494980)
% 0.21/0.46  ipcrm: permission denied for id (822444103)
% 0.21/0.47  ipcrm: permission denied for id (822476872)
% 0.21/0.47  ipcrm: permission denied for id (822509641)
% 0.21/0.47  ipcrm: permission denied for id (819593290)
% 0.21/0.47  ipcrm: permission denied for id (822542411)
% 0.21/0.47  ipcrm: permission denied for id (819626060)
% 0.21/0.48  ipcrm: permission denied for id (822607950)
% 0.21/0.48  ipcrm: permission denied for id (819757136)
% 0.21/0.48  ipcrm: permission denied for id (819822674)
% 0.21/0.48  ipcrm: permission denied for id (819855443)
% 0.21/0.48  ipcrm: permission denied for id (822706260)
% 0.21/0.49  ipcrm: permission denied for id (819920981)
% 0.21/0.49  ipcrm: permission denied for id (819953750)
% 0.21/0.49  ipcrm: permission denied for id (819986519)
% 0.21/0.49  ipcrm: permission denied for id (820052056)
% 0.21/0.49  ipcrm: permission denied for id (822739033)
% 0.21/0.49  ipcrm: permission denied for id (820117594)
% 0.21/0.50  ipcrm: permission denied for id (820248671)
% 0.21/0.50  ipcrm: permission denied for id (822935649)
% 0.21/0.51  ipcrm: permission denied for id (820314210)
% 0.21/0.51  ipcrm: permission denied for id (820346979)
% 0.21/0.51  ipcrm: permission denied for id (820379748)
% 0.21/0.51  ipcrm: permission denied for id (822968421)
% 0.21/0.51  ipcrm: permission denied for id (820412518)
% 0.21/0.51  ipcrm: permission denied for id (823001191)
% 0.21/0.51  ipcrm: permission denied for id (820445288)
% 0.21/0.52  ipcrm: permission denied for id (820478057)
% 0.21/0.52  ipcrm: permission denied for id (820510826)
% 0.21/0.52  ipcrm: permission denied for id (820543595)
% 0.21/0.52  ipcrm: permission denied for id (820576364)
% 0.21/0.52  ipcrm: permission denied for id (820609133)
% 0.21/0.52  ipcrm: permission denied for id (820674671)
% 0.36/0.53  ipcrm: permission denied for id (820740209)
% 0.36/0.53  ipcrm: permission denied for id (820772978)
% 0.36/0.53  ipcrm: permission denied for id (823132275)
% 0.36/0.53  ipcrm: permission denied for id (820838516)
% 0.36/0.54  ipcrm: permission denied for id (823197814)
% 0.36/0.54  ipcrm: permission denied for id (823230583)
% 0.36/0.54  ipcrm: permission denied for id (820969592)
% 0.36/0.54  ipcrm: permission denied for id (823263353)
% 0.36/0.54  ipcrm: permission denied for id (821035130)
% 0.37/0.54  ipcrm: permission denied for id (823296123)
% 0.37/0.54  ipcrm: permission denied for id (821067900)
% 0.40/0.66  % (23828)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.40/0.66  % (23827)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.40/0.66  % (23836)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.40/0.68  % (23835)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.40/0.69  % (23836)Refutation found. Thanks to Tanya!
% 0.40/0.69  % SZS status Theorem for theBenchmark
% 0.40/0.69  % (23821)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.40/0.70  % (23829)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.40/0.71  % (23838)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.40/0.71  % (23841)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.40/0.71  % (23831)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.40/0.71  % (23819)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.40/0.71  % (23837)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.40/0.71  % (23814)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.40/0.71  % SZS output start Proof for theBenchmark
% 0.40/0.71  fof(f410,plain,(
% 0.40/0.71    $false),
% 0.40/0.71    inference(subsumption_resolution,[],[f403,f176])).
% 0.40/0.71  fof(f176,plain,(
% 0.40/0.71    k1_xboole_0 != k1_tarski(sK0)),
% 0.40/0.71    inference(forward_demodulation,[],[f154,f56])).
% 0.40/0.71  fof(f56,plain,(
% 0.40/0.71    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.40/0.71    inference(cnf_transformation,[],[f11])).
% 0.40/0.71  fof(f11,axiom,(
% 0.40/0.71    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.40/0.71  fof(f154,plain,(
% 0.40/0.71    k1_relat_1(k1_xboole_0) != k1_tarski(sK0)),
% 0.40/0.71    inference(backward_demodulation,[],[f117,f139])).
% 0.40/0.71  fof(f139,plain,(
% 0.40/0.71    k1_xboole_0 = sK2),
% 0.40/0.71    inference(trivial_inequality_removal,[],[f136])).
% 0.40/0.71  fof(f136,plain,(
% 0.40/0.71    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.40/0.71    inference(superposition,[],[f99,f128])).
% 0.40/0.71  fof(f128,plain,(
% 0.40/0.71    k1_xboole_0 = k2_relat_1(sK2)),
% 0.40/0.71    inference(backward_demodulation,[],[f122,f127])).
% 0.40/0.71  fof(f127,plain,(
% 0.40/0.71    k1_xboole_0 = k11_relat_1(sK2,sK0)),
% 0.40/0.71    inference(subsumption_resolution,[],[f125,f95])).
% 0.40/0.71  fof(f95,plain,(
% 0.40/0.71    v1_relat_1(sK2)),
% 0.40/0.71    inference(resolution,[],[f53,f78])).
% 0.40/0.71  fof(f78,plain,(
% 0.40/0.71    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.71    inference(cnf_transformation,[],[f37])).
% 0.40/0.71  fof(f37,plain,(
% 0.40/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.71    inference(ennf_transformation,[],[f16])).
% 0.40/0.71  fof(f16,axiom,(
% 0.40/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.40/0.71  fof(f53,plain,(
% 0.40/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.40/0.71    inference(cnf_transformation,[],[f43])).
% 0.40/0.71  fof(f43,plain,(
% 0.40/0.71    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.40/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f42])).
% 0.40/0.71  fof(f42,plain,(
% 0.40/0.71    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.40/0.71    introduced(choice_axiom,[])).
% 0.40/0.71  fof(f23,plain,(
% 0.40/0.71    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.40/0.71    inference(flattening,[],[f22])).
% 0.40/0.71  fof(f22,plain,(
% 0.40/0.71    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.40/0.71    inference(ennf_transformation,[],[f21])).
% 0.40/0.71  fof(f21,negated_conjecture,(
% 0.40/0.71    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.40/0.71    inference(negated_conjecture,[],[f20])).
% 0.40/0.71  fof(f20,conjecture,(
% 0.40/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.40/0.71  fof(f125,plain,(
% 0.40/0.71    k1_xboole_0 = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(resolution,[],[f124,f66])).
% 0.40/0.71  fof(f66,plain,(
% 0.40/0.71    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f44])).
% 0.40/0.71  fof(f44,plain,(
% 0.40/0.71    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.40/0.71    inference(nnf_transformation,[],[f28])).
% 0.40/0.71  fof(f28,plain,(
% 0.40/0.71    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.40/0.71    inference(ennf_transformation,[],[f9])).
% 0.40/0.71  fof(f9,axiom,(
% 0.40/0.71    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.40/0.71  fof(f124,plain,(
% 0.40/0.71    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.40/0.71    inference(trivial_inequality_removal,[],[f123])).
% 0.40/0.71  fof(f123,plain,(
% 0.40/0.71    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.40/0.71    inference(backward_demodulation,[],[f119,f122])).
% 0.40/0.71  fof(f119,plain,(
% 0.40/0.71    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.40/0.71    inference(subsumption_resolution,[],[f118,f95])).
% 0.40/0.71  fof(f118,plain,(
% 0.40/0.71    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(subsumption_resolution,[],[f114,f51])).
% 0.40/0.71  fof(f51,plain,(
% 0.40/0.71    v1_funct_1(sK2)),
% 0.40/0.71    inference(cnf_transformation,[],[f43])).
% 0.40/0.71  fof(f114,plain,(
% 0.40/0.71    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(superposition,[],[f97,f67])).
% 0.40/0.71  fof(f67,plain,(
% 0.40/0.71    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f30])).
% 0.40/0.71  fof(f30,plain,(
% 0.40/0.71    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.40/0.71    inference(flattening,[],[f29])).
% 0.40/0.71  fof(f29,plain,(
% 0.40/0.71    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.40/0.71    inference(ennf_transformation,[],[f13])).
% 0.40/0.71  fof(f13,axiom,(
% 0.40/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.40/0.71  fof(f97,plain,(
% 0.40/0.71    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.40/0.71    inference(backward_demodulation,[],[f55,f94])).
% 0.40/0.71  fof(f94,plain,(
% 0.40/0.71    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.40/0.71    inference(resolution,[],[f53,f79])).
% 0.40/0.71  fof(f79,plain,(
% 0.40/0.71    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.71    inference(cnf_transformation,[],[f38])).
% 0.40/0.71  fof(f38,plain,(
% 0.40/0.71    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.71    inference(ennf_transformation,[],[f18])).
% 0.40/0.71  fof(f18,axiom,(
% 0.40/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.40/0.71  fof(f55,plain,(
% 0.40/0.71    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.40/0.71    inference(cnf_transformation,[],[f43])).
% 0.40/0.71  fof(f122,plain,(
% 0.40/0.71    k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 0.40/0.71    inference(subsumption_resolution,[],[f120,f95])).
% 0.40/0.71  fof(f120,plain,(
% 0.40/0.71    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(superposition,[],[f112,f62])).
% 0.40/0.71  fof(f62,plain,(
% 0.40/0.71    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f26])).
% 0.40/0.71  fof(f26,plain,(
% 0.40/0.71    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.40/0.71    inference(ennf_transformation,[],[f7])).
% 0.40/0.71  fof(f7,axiom,(
% 0.40/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.40/0.71  fof(f112,plain,(
% 0.40/0.71    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))),
% 0.40/0.71    inference(subsumption_resolution,[],[f111,f95])).
% 0.40/0.71  fof(f111,plain,(
% 0.40/0.71    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(superposition,[],[f64,f110])).
% 0.40/0.71  fof(f110,plain,(
% 0.40/0.71    sK2 = k7_relat_1(sK2,k1_tarski(sK0))),
% 0.40/0.71    inference(subsumption_resolution,[],[f109,f95])).
% 0.40/0.71  fof(f109,plain,(
% 0.40/0.71    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(resolution,[],[f93,f69])).
% 0.40/0.71  fof(f69,plain,(
% 0.40/0.71    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f34])).
% 0.40/0.71  fof(f34,plain,(
% 0.40/0.71    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.40/0.71    inference(flattening,[],[f33])).
% 0.40/0.71  fof(f33,plain,(
% 0.40/0.71    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.40/0.71    inference(ennf_transformation,[],[f10])).
% 0.40/0.71  fof(f10,axiom,(
% 0.40/0.71    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.40/0.71  fof(f93,plain,(
% 0.40/0.71    v4_relat_1(sK2,k1_tarski(sK0))),
% 0.40/0.71    inference(resolution,[],[f53,f80])).
% 0.40/0.71  fof(f80,plain,(
% 0.40/0.71    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.71    inference(cnf_transformation,[],[f39])).
% 0.40/0.71  fof(f39,plain,(
% 0.40/0.71    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.71    inference(ennf_transformation,[],[f17])).
% 0.40/0.71  fof(f17,axiom,(
% 0.40/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.40/0.71  fof(f64,plain,(
% 0.40/0.71    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f27])).
% 0.40/0.71  fof(f27,plain,(
% 0.40/0.71    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.40/0.71    inference(ennf_transformation,[],[f8])).
% 0.40/0.71  fof(f8,axiom,(
% 0.40/0.71    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.40/0.71  fof(f99,plain,(
% 0.40/0.71    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.40/0.71    inference(resolution,[],[f95,f61])).
% 0.40/0.71  fof(f61,plain,(
% 0.40/0.71    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f25])).
% 0.40/0.71  fof(f25,plain,(
% 0.40/0.71    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.40/0.71    inference(flattening,[],[f24])).
% 0.40/0.71  fof(f24,plain,(
% 0.40/0.71    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.40/0.71    inference(ennf_transformation,[],[f12])).
% 0.40/0.71  fof(f12,axiom,(
% 0.40/0.71    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.40/0.71  fof(f117,plain,(
% 0.40/0.71    k1_tarski(sK0) != k1_relat_1(sK2)),
% 0.40/0.71    inference(subsumption_resolution,[],[f116,f95])).
% 0.40/0.71  fof(f116,plain,(
% 0.40/0.71    k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(subsumption_resolution,[],[f115,f51])).
% 0.40/0.71  fof(f115,plain,(
% 0.40/0.71    k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(trivial_inequality_removal,[],[f113])).
% 0.40/0.71  fof(f113,plain,(
% 0.40/0.71    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.40/0.71    inference(superposition,[],[f97,f68])).
% 0.40/0.71  fof(f68,plain,(
% 0.40/0.71    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f32])).
% 0.40/0.71  fof(f32,plain,(
% 0.40/0.71    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.40/0.71    inference(flattening,[],[f31])).
% 0.40/0.71  fof(f31,plain,(
% 0.40/0.71    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.40/0.71    inference(ennf_transformation,[],[f14])).
% 0.40/0.71  fof(f14,axiom,(
% 0.40/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.40/0.71  fof(f403,plain,(
% 0.40/0.71    k1_xboole_0 = k1_tarski(sK0)),
% 0.40/0.71    inference(resolution,[],[f393,f58])).
% 0.40/0.71  fof(f58,plain,(
% 0.40/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f3])).
% 0.40/0.71  fof(f3,axiom,(
% 0.40/0.71    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.40/0.71  fof(f393,plain,(
% 0.40/0.71    ( ! [X3] : (~r1_tarski(X3,k1_tarski(sK0)) | k1_tarski(sK0) = X3) )),
% 0.40/0.71    inference(resolution,[],[f389,f72])).
% 0.40/0.71  fof(f72,plain,(
% 0.40/0.71    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f46])).
% 0.40/0.71  fof(f46,plain,(
% 0.40/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.40/0.71    inference(flattening,[],[f45])).
% 0.40/0.71  fof(f45,plain,(
% 0.40/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.40/0.71    inference(nnf_transformation,[],[f2])).
% 0.40/0.71  fof(f2,axiom,(
% 0.40/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.40/0.71  fof(f389,plain,(
% 0.40/0.71    ( ! [X2] : (r1_tarski(k1_tarski(sK0),X2)) )),
% 0.40/0.71    inference(resolution,[],[f380,f74])).
% 0.40/0.71  fof(f74,plain,(
% 0.40/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f50])).
% 0.40/0.71  fof(f50,plain,(
% 0.40/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.40/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 0.40/0.71  fof(f49,plain,(
% 0.40/0.71    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.40/0.71    introduced(choice_axiom,[])).
% 0.40/0.71  fof(f48,plain,(
% 0.40/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.40/0.71    inference(rectify,[],[f47])).
% 0.40/0.71  fof(f47,plain,(
% 0.40/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.40/0.71    inference(nnf_transformation,[],[f35])).
% 0.40/0.71  fof(f35,plain,(
% 0.40/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.40/0.71    inference(ennf_transformation,[],[f1])).
% 0.40/0.71  fof(f1,axiom,(
% 0.40/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.40/0.71  fof(f380,plain,(
% 0.40/0.71    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.40/0.71    inference(resolution,[],[f160,f321])).
% 0.40/0.71  fof(f321,plain,(
% 0.40/0.71    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.40/0.71    inference(trivial_inequality_removal,[],[f316])).
% 0.40/0.71  fof(f316,plain,(
% 0.40/0.71    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.40/0.71    inference(backward_demodulation,[],[f170,f314])).
% 0.40/0.71  fof(f314,plain,(
% 0.40/0.71    ( ! [X3] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X3)) )),
% 0.40/0.71    inference(subsumption_resolution,[],[f306,f58])).
% 0.40/0.71  fof(f306,plain,(
% 0.40/0.71    ( ! [X3] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X3) | ~r1_tarski(k1_xboole_0,X3)) )),
% 0.40/0.71    inference(resolution,[],[f172,f76])).
% 0.40/0.71  fof(f76,plain,(
% 0.40/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f36])).
% 0.40/0.71  fof(f36,plain,(
% 0.40/0.71    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.40/0.71    inference(ennf_transformation,[],[f15])).
% 0.40/0.71  fof(f15,axiom,(
% 0.40/0.71    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.40/0.71  fof(f172,plain,(
% 0.40/0.71    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | k1_xboole_0 = k11_relat_1(k1_xboole_0,X3)) )),
% 0.40/0.71    inference(forward_demodulation,[],[f171,f139])).
% 0.40/0.71  fof(f171,plain,(
% 0.40/0.71    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | k1_xboole_0 = k11_relat_1(sK2,X3)) )),
% 0.40/0.71    inference(forward_demodulation,[],[f150,f56])).
% 0.40/0.71  fof(f150,plain,(
% 0.40/0.71    ( ! [X3] : (r2_hidden(X3,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k11_relat_1(sK2,X3)) )),
% 0.40/0.71    inference(backward_demodulation,[],[f103,f139])).
% 0.40/0.71  fof(f103,plain,(
% 0.40/0.71    ( ! [X3] : (r2_hidden(X3,k1_relat_1(sK2)) | k1_xboole_0 = k11_relat_1(sK2,X3)) )),
% 0.40/0.71    inference(resolution,[],[f95,f66])).
% 0.40/0.71  fof(f170,plain,(
% 0.40/0.71    ( ! [X2] : (k1_xboole_0 != k11_relat_1(k1_xboole_0,X2) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.40/0.71    inference(forward_demodulation,[],[f169,f56])).
% 0.40/0.71  fof(f169,plain,(
% 0.40/0.71    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0)) | k1_xboole_0 != k11_relat_1(k1_xboole_0,X2)) )),
% 0.40/0.71    inference(forward_demodulation,[],[f149,f139])).
% 0.40/0.71  fof(f149,plain,(
% 0.40/0.71    ( ! [X2] : (k1_xboole_0 != k11_relat_1(k1_xboole_0,X2) | ~r2_hidden(X2,k1_relat_1(sK2))) )),
% 0.40/0.71    inference(backward_demodulation,[],[f102,f139])).
% 0.40/0.71  fof(f102,plain,(
% 0.40/0.71    ( ! [X2] : (k1_xboole_0 != k11_relat_1(sK2,X2) | ~r2_hidden(X2,k1_relat_1(sK2))) )),
% 0.40/0.71    inference(resolution,[],[f95,f65])).
% 0.40/0.71  fof(f65,plain,(
% 0.40/0.71    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f44])).
% 0.40/0.71  fof(f160,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.40/0.71    inference(backward_demodulation,[],[f131,f139])).
% 0.40/0.71  fof(f131,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_xboole_0) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.40/0.71    inference(backward_demodulation,[],[f96,f128])).
% 0.40/0.71  fof(f96,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.40/0.71    inference(backward_demodulation,[],[f91,f94])).
% 0.40/0.71  fof(f91,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.40/0.71    inference(subsumption_resolution,[],[f90,f51])).
% 0.40/0.71  fof(f90,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0)) | ~v1_funct_1(sK2)) )),
% 0.40/0.71    inference(subsumption_resolution,[],[f89,f53])).
% 0.40/0.71  fof(f89,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK2)) )),
% 0.40/0.71    inference(subsumption_resolution,[],[f88,f54])).
% 0.40/0.71  fof(f54,plain,(
% 0.40/0.71    k1_xboole_0 != sK1),
% 0.40/0.71    inference(cnf_transformation,[],[f43])).
% 0.40/0.71  fof(f88,plain,(
% 0.40/0.71    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK2)) )),
% 0.40/0.71    inference(resolution,[],[f52,f82])).
% 0.40/0.71  fof(f82,plain,(
% 0.40/0.71    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.40/0.71    inference(cnf_transformation,[],[f41])).
% 0.40/0.71  fof(f41,plain,(
% 0.40/0.71    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.40/0.71    inference(flattening,[],[f40])).
% 0.40/0.71  fof(f40,plain,(
% 0.40/0.71    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.40/0.71    inference(ennf_transformation,[],[f19])).
% 0.40/0.71  fof(f19,axiom,(
% 0.40/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.40/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.40/0.71  fof(f52,plain,(
% 0.40/0.71    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.40/0.71    inference(cnf_transformation,[],[f43])).
% 0.40/0.71  % SZS output end Proof for theBenchmark
% 0.40/0.71  % (23836)------------------------------
% 0.40/0.71  % (23836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.71  % (23836)Termination reason: Refutation
% 0.40/0.71  
% 0.40/0.71  % (23836)Memory used [KB]: 1918
% 0.40/0.71  % (23836)Time elapsed: 0.070 s
% 0.40/0.71  % (23836)------------------------------
% 0.40/0.71  % (23836)------------------------------
% 0.40/0.71  % (23642)Success in time 0.352 s
%------------------------------------------------------------------------------
