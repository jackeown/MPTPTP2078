%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 260 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  244 ( 663 expanded)
%              Number of equality atoms :   88 ( 303 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1264,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1263,f276])).

fof(f276,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f275,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f275,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f180,f245])).

fof(f245,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f136,f236])).

fof(f236,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f142,f126])).

fof(f126,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f142,plain,(
    ! [X2] :
      ( ~ v4_relat_1(sK2,X2)
      | sK2 = k7_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f75,f95])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f136,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f67,f95])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f180,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f179,f163])).

fof(f163,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f179,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f178,f167])).

fof(f167,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f178,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f177,f161])).

fof(f161,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f177,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK2),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f176,f165])).

fof(f165,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f86,f55])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f176,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relset_1(sK0,sK1,sK2),k7_relset_1(sK0,sK1,sK2,sK0))
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f175,f165])).

fof(f175,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK0),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relset_1(sK0,sK1,sK2),k7_relset_1(sK0,sK1,sK2,sK0))
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f173,f161])).

fof(f173,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK0),k2_relset_1(sK0,sK1,sK2))
    | ~ r1_tarski(k2_relset_1(sK0,sK1,sK2),k7_relset_1(sK0,sK1,sK2,sK0))
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(extensionality_resolution,[],[f78,f56])).

fof(f56,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1263,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f1258,f338])).

fof(f338,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f332,f95])).

fof(f332,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f328,f122])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))
      | k1_relat_1(X1) = k10_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f328,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f323,f98])).

fof(f98,plain,(
    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(resolution,[],[f63,f95])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f323,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))) ),
    inference(resolution,[],[f154,f89])).

fof(f154,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_relat_1(sK2))
      | r1_tarski(X2,k10_relat_1(sK2,k9_relat_1(sK2,X2))) ) ),
    inference(resolution,[],[f69,f95])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1258,plain,(
    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f150,f1212])).

fof(f1212,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f1175,f61])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1175,plain,(
    k3_xboole_0(k2_relat_1(sK2),sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f61,f645])).

fof(f645,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(k3_xboole_0(k2_relat_1(sK2),sK1)) ),
    inference(resolution,[],[f309,f128])).

fof(f128,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f85,f55])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f309,plain,(
    ! [X4] :
      ( ~ v5_relat_1(sK2,X4)
      | k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(k3_xboole_0(k2_relat_1(sK2),X4)) ) ),
    inference(resolution,[],[f213,f102])).

fof(f102,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(sK2),X2)
      | ~ v5_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f70,f95])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f213,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k6_relat_1(k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f144,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_relat_1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f113,f61])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | v4_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f141,f133])).

fof(f133,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f130,f64])).

fof(f64,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f130,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f75,f57])).

fof(f150,plain,(
    ! [X2] : k10_relat_1(sK2,X2) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X2)) ),
    inference(resolution,[],[f68,f95])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (17525)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (17510)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (17531)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (17522)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (17514)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (17511)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (17516)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (17522)Refutation not found, incomplete strategy% (17522)------------------------------
% 0.21/0.50  % (17522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17515)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (17521)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (17509)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (17514)Refutation not found, incomplete strategy% (17514)------------------------------
% 0.21/0.50  % (17514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17522)Memory used [KB]: 6268
% 0.21/0.50  % (17522)Time elapsed: 0.095 s
% 0.21/0.50  % (17522)------------------------------
% 0.21/0.50  % (17522)------------------------------
% 0.21/0.50  % (17514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17514)Memory used [KB]: 6268
% 0.21/0.50  % (17514)Time elapsed: 0.099 s
% 0.21/0.50  % (17514)------------------------------
% 0.21/0.50  % (17514)------------------------------
% 0.21/0.50  % (17533)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (17512)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (17530)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (17529)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (17518)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (17519)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (17526)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (17532)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (17520)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (17534)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (17517)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (17515)Refutation not found, incomplete strategy% (17515)------------------------------
% 0.21/0.52  % (17515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17515)Memory used [KB]: 10618
% 0.21/0.52  % (17515)Time elapsed: 0.062 s
% 0.21/0.52  % (17515)------------------------------
% 0.21/0.52  % (17515)------------------------------
% 0.21/0.52  % (17513)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (17523)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (17527)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (17509)Refutation not found, incomplete strategy% (17509)------------------------------
% 0.21/0.52  % (17509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17509)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17509)Memory used [KB]: 10746
% 0.21/0.52  % (17509)Time elapsed: 0.097 s
% 0.21/0.52  % (17509)------------------------------
% 0.21/0.52  % (17509)------------------------------
% 0.21/0.53  % (17524)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (17528)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (17520)Refutation not found, incomplete strategy% (17520)------------------------------
% 0.21/0.54  % (17520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17520)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17520)Memory used [KB]: 10746
% 0.21/0.54  % (17520)Time elapsed: 0.123 s
% 0.21/0.54  % (17520)------------------------------
% 0.21/0.54  % (17520)------------------------------
% 0.21/0.56  % (17525)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1264,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f1263,f276])).
% 0.21/0.56  fof(f276,plain,(
% 0.21/0.56    k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.21/0.56    inference(subsumption_resolution,[],[f275,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f275,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f274])).
% 0.21/0.56  fof(f274,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.21/0.56    inference(superposition,[],[f180,f245])).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.21/0.56    inference(superposition,[],[f136,f236])).
% 0.21/0.56  fof(f236,plain,(
% 0.21/0.56    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.56    inference(resolution,[],[f142,f126])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    v4_relat_1(sK2,sK0)),
% 0.21/0.56    inference(resolution,[],[f84,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.56    inference(negated_conjecture,[],[f24])).
% 0.21/0.56  fof(f24,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ( ! [X2] : (~v4_relat_1(sK2,X2) | sK2 = k7_relat_1(sK2,X2)) )),
% 0.21/0.56    inference(resolution,[],[f75,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f81,f55])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 0.21/0.56    inference(resolution,[],[f67,f95])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    ~r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f179,f163])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f83,f55])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.56    inference(forward_demodulation,[],[f178,f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f87,f55])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f177,f161])).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f82,f55])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    ~r1_tarski(k2_relset_1(sK0,sK1,sK2),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f176,f165])).
% 0.21/0.56  fof(f165,plain,(
% 0.21/0.56    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f86,f55])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    ~r1_tarski(k9_relat_1(sK2,sK0),k2_relat_1(sK2)) | ~r1_tarski(k2_relset_1(sK0,sK1,sK2),k7_relset_1(sK0,sK1,sK2,sK0)) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f175,f165])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK0),k2_relat_1(sK2)) | ~r1_tarski(k2_relset_1(sK0,sK1,sK2),k7_relset_1(sK0,sK1,sK2,sK0)) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f173,f161])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK0),k2_relset_1(sK0,sK1,sK2)) | ~r1_tarski(k2_relset_1(sK0,sK1,sK2),k7_relset_1(sK0,sK1,sK2,sK0)) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.56    inference(extensionality_resolution,[],[f78,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f53])).
% 0.21/0.56  fof(f1263,plain,(
% 0.21/0.56    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f1258,f338])).
% 0.21/0.56  fof(f338,plain,(
% 0.21/0.56    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f332,f95])).
% 0.21/0.56  fof(f332,plain,(
% 0.21/0.56    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f328,f122])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) | k1_relat_1(X1) = k10_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(resolution,[],[f78,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.56  fof(f328,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))),
% 0.21/0.56    inference(forward_demodulation,[],[f323,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f63,f95])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))))),
% 0.21/0.56    inference(resolution,[],[f154,f89])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(sK2)) | r1_tarski(X2,k10_relat_1(sK2,k9_relat_1(sK2,X2)))) )),
% 0.21/0.56    inference(resolution,[],[f69,f95])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.57  fof(f1258,plain,(
% 0.21/0.57    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.57    inference(superposition,[],[f150,f1212])).
% 0.21/0.57  fof(f1212,plain,(
% 0.21/0.57    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f1175,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.57  fof(f1175,plain,(
% 0.21/0.57    k3_xboole_0(k2_relat_1(sK2),sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.21/0.57    inference(superposition,[],[f61,f645])).
% 0.21/0.57  fof(f645,plain,(
% 0.21/0.57    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(k3_xboole_0(k2_relat_1(sK2),sK1))),
% 0.21/0.57    inference(resolution,[],[f309,f128])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    v5_relat_1(sK2,sK1)),
% 0.21/0.57    inference(resolution,[],[f85,f55])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    ( ! [X4] : (~v5_relat_1(sK2,X4) | k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(k3_xboole_0(k2_relat_1(sK2),X4))) )),
% 0.21/0.57    inference(resolution,[],[f213,f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X2] : (r1_tarski(k2_relat_1(sK2),X2) | ~v5_relat_1(sK2,X2)) )),
% 0.21/0.57    inference(resolution,[],[f70,f95])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k6_relat_1(k3_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(resolution,[],[f144,f115])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v4_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f113,f61])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | v4_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.57    inference(resolution,[],[f73,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f141,f133])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f130,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.57    inference(resolution,[],[f66,f57])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.57    inference(resolution,[],[f75,f57])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    ( ! [X2] : (k10_relat_1(sK2,X2) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X2))) )),
% 0.21/0.57    inference(resolution,[],[f68,f95])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (17525)------------------------------
% 0.21/0.57  % (17525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (17525)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (17525)Memory used [KB]: 2430
% 0.21/0.57  % (17525)Time elapsed: 0.143 s
% 0.21/0.57  % (17525)------------------------------
% 0.21/0.57  % (17525)------------------------------
% 0.21/0.57  % (17508)Success in time 0.213 s
%------------------------------------------------------------------------------
