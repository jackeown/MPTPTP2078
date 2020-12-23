%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:16 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 503 expanded)
%              Number of leaves         :   18 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          :  234 (1311 expanded)
%              Number of equality atoms :   82 ( 545 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(subsumption_resolution,[],[f416,f277])).

fof(f277,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f276,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f276,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f275,f166])).

fof(f166,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f76,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),X3)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) ) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f275,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ) ),
    inference(superposition,[],[f174,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f174,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) ),
    inference(resolution,[],[f166,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f416,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f203,f243])).

fof(f243,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK0) ),
    inference(superposition,[],[f240,f122])).

fof(f122,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f68])).

fof(f68,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f121,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f46,f96])).

fof(f96,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f90,f68])).

fof(f90,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f72,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f43,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f240,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f237,f75])).

fof(f75,plain,(
    ! [X2] : k8_relset_1(sK1,sK0,sK2,X2) = k10_relat_1(sK2,X2) ),
    inference(resolution,[],[f43,f64])).

fof(f237,plain,(
    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f195,f220])).

fof(f220,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f213,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f143,f68])).

fof(f143,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) = k9_relat_1(sK2,X0)
      | ~ v4_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f87,plain,(
    ! [X5] : k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5) ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f213,plain,(
    v4_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f201,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f201,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK0),sK0))) ),
    inference(resolution,[],[f199,f76])).

fof(f199,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f198,f122])).

fof(f198,plain,(
    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f197,f68])).

fof(f197,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f196,f67])).

fof(f196,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f47,f182])).

fof(f182,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f172,f147])).

fof(f172,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f166,f60])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f195,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f194,f102])).

fof(f102,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f101,f68])).

fof(f101,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f45,f89])).

fof(f89,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f88,f68])).

fof(f88,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f43,f60])).

fof(f194,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f193,f74])).

fof(f74,plain,(
    ! [X1] : k7_relset_1(sK1,sK0,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f43,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f193,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f119,f74])).

fof(f119,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f111,f64])).

fof(f111,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f106,f70])).

fof(f70,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f106,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f44,f69])).

fof(f69,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f44,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f203,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f199,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:31:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (24958)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (24957)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (24966)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (24960)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (24975)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (24976)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.55  % (24973)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (24964)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (24974)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  % (24968)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (24956)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (24967)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (24959)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (24962)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.56  % (24960)Refutation not found, incomplete strategy% (24960)------------------------------
% 0.22/0.56  % (24960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24960)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (24960)Memory used [KB]: 10618
% 0.22/0.56  % (24960)Time elapsed: 0.116 s
% 0.22/0.56  % (24960)------------------------------
% 0.22/0.56  % (24960)------------------------------
% 0.22/0.56  % (24965)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (24959)Refutation not found, incomplete strategy% (24959)------------------------------
% 0.22/0.56  % (24959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (24978)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.53/0.57  % (24972)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.53/0.57  % (24959)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (24959)Memory used [KB]: 6268
% 1.53/0.57  % (24959)Time elapsed: 0.123 s
% 1.53/0.57  % (24959)------------------------------
% 1.53/0.57  % (24959)------------------------------
% 1.53/0.57  % (24962)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % (24970)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.53/0.58  % (24955)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.58  % (24961)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.67/0.58  % (24967)Refutation not found, incomplete strategy% (24967)------------------------------
% 1.67/0.58  % (24967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (24967)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (24967)Memory used [KB]: 6396
% 1.67/0.58  % (24967)Time elapsed: 0.136 s
% 1.67/0.58  % (24967)------------------------------
% 1.67/0.58  % (24967)------------------------------
% 1.67/0.59  % (24979)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.67/0.59  % (24971)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.67/0.59  % SZS output start Proof for theBenchmark
% 1.67/0.59  fof(f417,plain,(
% 1.67/0.59    $false),
% 1.67/0.59    inference(subsumption_resolution,[],[f416,f277])).
% 1.67/0.59  fof(f277,plain,(
% 1.67/0.59    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))) )),
% 1.67/0.59    inference(resolution,[],[f276,f55])).
% 1.67/0.59  fof(f55,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f42])).
% 1.67/0.59  fof(f42,plain,(
% 1.67/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.67/0.59    inference(nnf_transformation,[],[f3])).
% 1.67/0.59  fof(f3,axiom,(
% 1.67/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.67/0.59  fof(f276,plain,(
% 1.67/0.59    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2)))) )),
% 1.67/0.59    inference(subsumption_resolution,[],[f275,f166])).
% 1.67/0.59  fof(f166,plain,(
% 1.67/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 1.67/0.59    inference(resolution,[],[f76,f67])).
% 1.67/0.59  fof(f67,plain,(
% 1.67/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.67/0.59    inference(equality_resolution,[],[f52])).
% 1.67/0.59  fof(f52,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.67/0.59    inference(cnf_transformation,[],[f41])).
% 1.67/0.59  fof(f41,plain,(
% 1.67/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.59    inference(flattening,[],[f40])).
% 1.67/0.59  fof(f40,plain,(
% 1.67/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.59    inference(nnf_transformation,[],[f1])).
% 1.67/0.59  fof(f1,axiom,(
% 1.67/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.59  fof(f76,plain,(
% 1.67/0.59    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),X3) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))) )),
% 1.67/0.59    inference(resolution,[],[f43,f65])).
% 1.67/0.59  fof(f65,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f36])).
% 1.67/0.59  fof(f36,plain,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.67/0.59    inference(flattening,[],[f35])).
% 1.67/0.59  fof(f35,plain,(
% 1.67/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.67/0.59    inference(ennf_transformation,[],[f16])).
% 1.67/0.59  fof(f16,axiom,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 1.67/0.59  fof(f43,plain,(
% 1.67/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.67/0.59    inference(cnf_transformation,[],[f38])).
% 1.67/0.59  fof(f38,plain,(
% 1.67/0.59    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f19,plain,(
% 1.67/0.59    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.67/0.59    inference(ennf_transformation,[],[f18])).
% 1.67/0.59  fof(f18,negated_conjecture,(
% 1.67/0.59    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.67/0.59    inference(negated_conjecture,[],[f17])).
% 1.67/0.59  fof(f17,conjecture,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 1.67/0.59  fof(f275,plain,(
% 1.67/0.59    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k1_relat_1(sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))) )),
% 1.67/0.59    inference(superposition,[],[f174,f64])).
% 1.67/0.59  fof(f64,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f34])).
% 1.67/0.59  fof(f34,plain,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f15])).
% 1.67/0.59  fof(f15,axiom,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.67/0.59  fof(f174,plain,(
% 1.67/0.59    ( ! [X0] : (m1_subset_1(k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0),k1_zfmisc_1(k1_relat_1(sK2)))) )),
% 1.67/0.59    inference(resolution,[],[f166,f62])).
% 1.67/0.59  fof(f62,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f32])).
% 1.67/0.59  fof(f32,plain,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f11])).
% 1.67/0.59  fof(f11,axiom,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.67/0.59  fof(f416,plain,(
% 1.67/0.59    ~r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2))),
% 1.67/0.59    inference(subsumption_resolution,[],[f203,f243])).
% 1.67/0.59  fof(f243,plain,(
% 1.67/0.59    k1_relat_1(sK2) != k10_relat_1(sK2,sK0)),
% 1.67/0.59    inference(superposition,[],[f240,f122])).
% 1.67/0.59  fof(f122,plain,(
% 1.67/0.59    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.67/0.59    inference(subsumption_resolution,[],[f121,f68])).
% 1.67/0.59  fof(f68,plain,(
% 1.67/0.59    v1_relat_1(sK2)),
% 1.67/0.59    inference(resolution,[],[f43,f57])).
% 1.67/0.59  fof(f57,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f28])).
% 1.67/0.59  fof(f28,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f9])).
% 1.67/0.59  fof(f9,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.67/0.59  fof(f121,plain,(
% 1.67/0.59    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.67/0.59    inference(superposition,[],[f46,f96])).
% 1.67/0.59  fof(f96,plain,(
% 1.67/0.59    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)),
% 1.67/0.59    inference(resolution,[],[f91,f50])).
% 1.67/0.59  fof(f50,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f25])).
% 1.67/0.59  fof(f25,plain,(
% 1.67/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f2])).
% 1.67/0.59  fof(f2,axiom,(
% 1.67/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.67/0.59  fof(f91,plain,(
% 1.67/0.59    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.67/0.59    inference(subsumption_resolution,[],[f90,f68])).
% 1.67/0.59  fof(f90,plain,(
% 1.67/0.59    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.67/0.59    inference(resolution,[],[f72,f48])).
% 1.67/0.59  fof(f48,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f39])).
% 1.67/0.59  fof(f39,plain,(
% 1.67/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(nnf_transformation,[],[f24])).
% 1.67/0.59  fof(f24,plain,(
% 1.67/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f4])).
% 1.67/0.59  fof(f4,axiom,(
% 1.67/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.67/0.59  fof(f72,plain,(
% 1.67/0.59    v5_relat_1(sK2,sK0)),
% 1.67/0.59    inference(resolution,[],[f43,f61])).
% 1.67/0.59  fof(f61,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f31])).
% 1.67/0.59  fof(f31,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f10])).
% 1.67/0.59  fof(f10,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.67/0.59  fof(f46,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f21])).
% 1.67/0.59  fof(f21,plain,(
% 1.67/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f6])).
% 1.67/0.59  fof(f6,axiom,(
% 1.67/0.59    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.67/0.59  fof(f240,plain,(
% 1.67/0.59    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.67/0.59    inference(superposition,[],[f237,f75])).
% 1.67/0.59  fof(f75,plain,(
% 1.67/0.59    ( ! [X2] : (k8_relset_1(sK1,sK0,sK2,X2) = k10_relat_1(sK2,X2)) )),
% 1.67/0.59    inference(resolution,[],[f43,f64])).
% 1.67/0.59  fof(f237,plain,(
% 1.67/0.59    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 1.67/0.59    inference(trivial_inequality_removal,[],[f235])).
% 1.67/0.59  fof(f235,plain,(
% 1.67/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 1.67/0.59    inference(backward_demodulation,[],[f195,f220])).
% 1.67/0.59  fof(f220,plain,(
% 1.67/0.59    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.67/0.59    inference(resolution,[],[f213,f147])).
% 1.67/0.59  fof(f147,plain,(
% 1.67/0.59    ( ! [X0] : (~v4_relat_1(sK2,X0) | k2_relat_1(sK2) = k9_relat_1(sK2,X0)) )),
% 1.67/0.59    inference(subsumption_resolution,[],[f143,f68])).
% 1.67/0.59  fof(f143,plain,(
% 1.67/0.59    ( ! [X0] : (k2_relat_1(sK2) = k9_relat_1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 1.67/0.59    inference(superposition,[],[f87,f51])).
% 1.67/0.59  fof(f51,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f27,plain,(
% 1.67/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(flattening,[],[f26])).
% 1.67/0.59  fof(f26,plain,(
% 1.67/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.67/0.59    inference(ennf_transformation,[],[f7])).
% 1.67/0.59  fof(f7,axiom,(
% 1.67/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.67/0.59  fof(f87,plain,(
% 1.67/0.59    ( ! [X5] : (k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5)) )),
% 1.67/0.59    inference(resolution,[],[f68,f45])).
% 1.67/0.59  fof(f45,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f5])).
% 1.67/0.59  fof(f5,axiom,(
% 1.67/0.59    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.67/0.59  fof(f213,plain,(
% 1.67/0.59    v4_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.67/0.59    inference(resolution,[],[f201,f60])).
% 1.67/0.59  fof(f60,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f31])).
% 1.67/0.59  fof(f201,plain,(
% 1.67/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK0),sK0)))),
% 1.67/0.59    inference(resolution,[],[f199,f76])).
% 1.67/0.59  fof(f199,plain,(
% 1.67/0.59    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))),
% 1.67/0.59    inference(forward_demodulation,[],[f198,f122])).
% 1.67/0.59  fof(f198,plain,(
% 1.67/0.59    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))),
% 1.67/0.59    inference(subsumption_resolution,[],[f197,f68])).
% 1.67/0.59  fof(f197,plain,(
% 1.67/0.59    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(sK2)),
% 1.67/0.59    inference(subsumption_resolution,[],[f196,f67])).
% 1.67/0.59  fof(f196,plain,(
% 1.67/0.59    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.67/0.59    inference(superposition,[],[f47,f182])).
% 1.67/0.59  fof(f182,plain,(
% 1.67/0.59    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.67/0.59    inference(resolution,[],[f172,f147])).
% 1.67/0.59  fof(f172,plain,(
% 1.67/0.59    v4_relat_1(sK2,k1_relat_1(sK2))),
% 1.67/0.59    inference(resolution,[],[f166,f60])).
% 1.67/0.59  fof(f47,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f23])).
% 1.67/0.59  fof(f23,plain,(
% 1.67/0.59    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(flattening,[],[f22])).
% 1.67/0.59  fof(f22,plain,(
% 1.67/0.59    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f8])).
% 1.67/0.59  fof(f8,axiom,(
% 1.67/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.67/0.59  fof(f195,plain,(
% 1.67/0.59    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 1.67/0.59    inference(forward_demodulation,[],[f194,f102])).
% 1.67/0.59  fof(f102,plain,(
% 1.67/0.59    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 1.67/0.59    inference(subsumption_resolution,[],[f101,f68])).
% 1.67/0.59  fof(f101,plain,(
% 1.67/0.59    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.67/0.59    inference(superposition,[],[f45,f89])).
% 1.67/0.59  fof(f89,plain,(
% 1.67/0.59    sK2 = k7_relat_1(sK2,sK1)),
% 1.67/0.59    inference(subsumption_resolution,[],[f88,f68])).
% 1.67/0.59  fof(f88,plain,(
% 1.67/0.59    sK2 = k7_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.67/0.59    inference(resolution,[],[f71,f51])).
% 1.67/0.59  fof(f71,plain,(
% 1.67/0.59    v4_relat_1(sK2,sK1)),
% 1.67/0.59    inference(resolution,[],[f43,f60])).
% 1.67/0.59  fof(f194,plain,(
% 1.67/0.59    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.67/0.59    inference(forward_demodulation,[],[f193,f74])).
% 1.67/0.59  fof(f74,plain,(
% 1.67/0.59    ( ! [X1] : (k7_relset_1(sK1,sK0,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 1.67/0.59    inference(resolution,[],[f43,f63])).
% 1.67/0.59  fof(f63,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f33])).
% 1.67/0.59  fof(f33,plain,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f14])).
% 1.67/0.59  fof(f14,axiom,(
% 1.67/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.67/0.59  fof(f193,plain,(
% 1.67/0.59    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.67/0.59    inference(forward_demodulation,[],[f119,f74])).
% 1.67/0.59  fof(f119,plain,(
% 1.67/0.59    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.67/0.59    inference(subsumption_resolution,[],[f117,f43])).
% 1.67/0.59  fof(f117,plain,(
% 1.67/0.59    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.67/0.59    inference(superposition,[],[f111,f64])).
% 1.67/0.59  fof(f111,plain,(
% 1.67/0.59    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.67/0.59    inference(backward_demodulation,[],[f106,f70])).
% 1.67/0.59  fof(f70,plain,(
% 1.67/0.59    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.67/0.59    inference(resolution,[],[f43,f59])).
% 1.67/0.59  fof(f59,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f30])).
% 1.67/0.59  fof(f30,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f13])).
% 1.67/0.59  fof(f13,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.67/0.59  fof(f106,plain,(
% 1.67/0.59    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.67/0.59    inference(backward_demodulation,[],[f44,f69])).
% 1.67/0.59  fof(f69,plain,(
% 1.67/0.59    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.67/0.59    inference(resolution,[],[f43,f58])).
% 1.67/0.59  fof(f58,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f29])).
% 1.67/0.59  fof(f29,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.59    inference(ennf_transformation,[],[f12])).
% 1.67/0.59  fof(f12,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.67/0.59  fof(f44,plain,(
% 1.67/0.59    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)),
% 1.67/0.59    inference(cnf_transformation,[],[f38])).
% 1.67/0.59  fof(f203,plain,(
% 1.67/0.59    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2))),
% 1.67/0.59    inference(resolution,[],[f199,f54])).
% 1.67/0.59  fof(f54,plain,(
% 1.67/0.59    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f41])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (24962)------------------------------
% 1.67/0.59  % (24962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (24962)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (24962)Memory used [KB]: 1791
% 1.67/0.59  % (24962)Time elapsed: 0.117 s
% 1.67/0.59  % (24962)------------------------------
% 1.67/0.59  % (24962)------------------------------
% 1.67/0.59  % (24953)Success in time 0.221 s
%------------------------------------------------------------------------------
