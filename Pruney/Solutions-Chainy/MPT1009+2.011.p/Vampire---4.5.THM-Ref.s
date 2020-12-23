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
% DateTime   : Thu Dec  3 13:04:27 EST 2020

% Result     : Theorem 9.94s
% Output     : Refutation 10.62s
% Verified   : 
% Statistics : Number of formulae       :  112 (1335 expanded)
%              Number of leaves         :   22 ( 396 expanded)
%              Depth                    :   21
%              Number of atoms          :  228 (2219 expanded)
%              Number of equality atoms :   59 (1104 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9454,plain,(
    $false ),
    inference(global_subsumption,[],[f9432,f9436])).

fof(f9436,plain,(
    r2_hidden(sK4(k9_relat_1(sK3,sK2),k2_relat_1(sK3)),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f1117,f9389])).

fof(f9389,plain,(
    k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f42,f117,f9033,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f54,f90,f90])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f82,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f9033,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f606,f7844,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7844,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f3609,f7836])).

fof(f7836,plain,(
    sK0 = sK4(k1_relat_1(sK3),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f7832])).

fof(f7832,plain,
    ( sK0 = sK4(k1_relat_1(sK3),k1_xboole_0)
    | sK0 = sK4(k1_relat_1(sK3),k1_xboole_0) ),
    inference(resolution,[],[f7806,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f7806,plain,(
    sP6(sK4(k1_relat_1(sK3),k1_xboole_0),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f3414,f606,f1120])).

fof(f1120,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_tarski(X6,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))
      | r1_tarski(X6,X9)
      | sP6(sK4(X6,X9),X8,X7) ) ),
    inference(resolution,[],[f157,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3414,plain,(
    ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3393,f568])).

fof(f568,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f446,f103])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f446,plain,(
    ! [X19] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,sK1)))
      | ~ r1_tarski(k1_relat_1(sK3),X19) ) ),
    inference(resolution,[],[f80,f92])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f44,f90])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f3393,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f310,f1891])).

fof(f1891,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k9_relat_1(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f299,f103])).

fof(f299,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f310,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))) ),
    inference(unit_resulting_resolution,[],[f302,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f302,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f91,f295])).

fof(f295,plain,(
    ! [X0] : k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f92,f79])).

fof(f91,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f46,f90,f90])).

fof(f46,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f3609,plain,(
    r1_tarski(k6_enumset1(sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0)),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f3443,f319])).

fof(f319,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f94,f62])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f90])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f3443,plain,(
    r2_hidden(sK4(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f3414,f59])).

fof(f606,plain,(
    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f117,f158,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f158,plain,(
    v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f92,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f92,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f1117,plain,(
    r2_hidden(sK4(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f302,f315,f157])).

fof(f315,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f301,f62])).

fof(f301,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(backward_demodulation,[],[f286,f296])).

fof(f296,plain,(
    ! [X0] : k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f229,f79])).

fof(f229,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    inference(unit_resulting_resolution,[],[f117,f42,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f286,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(unit_resulting_resolution,[],[f229,f78])).

fof(f9432,plain,(
    ~ r2_hidden(sK4(k9_relat_1(sK3,sK2),k2_relat_1(sK3)),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f308,f9389])).

fof(f308,plain,(
    ~ r2_hidden(sK4(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(unit_resulting_resolution,[],[f302,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (18504)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (18518)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (18508)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (18508)Refutation not found, incomplete strategy% (18508)------------------------------
% 0.20/0.52  % (18508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18508)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18508)Memory used [KB]: 10746
% 0.20/0.52  % (18508)Time elapsed: 0.119 s
% 0.20/0.52  % (18508)------------------------------
% 0.20/0.52  % (18508)------------------------------
% 0.20/0.53  % (18515)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (18524)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (18501)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (18499)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (18507)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (18522)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.57  % (18521)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.58  % (18513)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.58  % (18522)Refutation not found, incomplete strategy% (18522)------------------------------
% 0.20/0.58  % (18522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (18522)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (18522)Memory used [KB]: 1791
% 0.20/0.58  % (18522)Time elapsed: 0.158 s
% 0.20/0.58  % (18522)------------------------------
% 0.20/0.58  % (18522)------------------------------
% 0.20/0.58  % (18532)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.58  % (18530)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.58  % (18516)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.59  % (18506)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.59  % (18502)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.59  % (18502)Refutation not found, incomplete strategy% (18502)------------------------------
% 0.20/0.59  % (18502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (18499)Refutation not found, incomplete strategy% (18499)------------------------------
% 0.20/0.59  % (18499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (18499)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (18499)Memory used [KB]: 1791
% 0.20/0.59  % (18499)Time elapsed: 0.194 s
% 0.20/0.59  % (18499)------------------------------
% 0.20/0.59  % (18499)------------------------------
% 0.20/0.59  % (18502)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (18502)Memory used [KB]: 10746
% 0.20/0.59  % (18502)Time elapsed: 0.167 s
% 0.20/0.59  % (18502)------------------------------
% 0.20/0.59  % (18502)------------------------------
% 0.20/0.59  % (18521)Refutation not found, incomplete strategy% (18521)------------------------------
% 0.20/0.59  % (18521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (18521)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (18521)Memory used [KB]: 10874
% 0.20/0.59  % (18521)Time elapsed: 0.171 s
% 0.20/0.59  % (18521)------------------------------
% 0.20/0.59  % (18521)------------------------------
% 0.20/0.59  % (18526)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.60  % (18510)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.60  % (18527)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.60  % (18503)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.60  % (18520)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.96/0.62  % (18531)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.96/0.62  % (18509)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.96/0.63  % (18512)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.96/0.63  % (18514)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.96/0.64  % (18505)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.96/0.64  % (18517)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.96/0.64  % (18529)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.15/0.64  % (18511)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.15/0.64  % (18525)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.21/0.70  % (18554)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.58/0.71  % (18556)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.58/0.75  % (18555)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.91/0.77  % (18557)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.91/0.79  % (18558)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.54/0.86  % (18505)Time limit reached!
% 3.54/0.86  % (18505)------------------------------
% 3.54/0.86  % (18505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.54/0.86  % (18505)Termination reason: Time limit
% 3.54/0.86  
% 3.54/0.86  % (18505)Memory used [KB]: 7803
% 3.54/0.86  % (18505)Time elapsed: 0.402 s
% 3.54/0.86  % (18505)------------------------------
% 3.54/0.86  % (18505)------------------------------
% 3.83/0.92  % (18501)Time limit reached!
% 3.83/0.92  % (18501)------------------------------
% 3.83/0.92  % (18501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.92  % (18510)Time limit reached!
% 3.83/0.92  % (18510)------------------------------
% 3.83/0.92  % (18510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.93  % (18501)Termination reason: Time limit
% 3.83/0.93  % (18501)Termination phase: Saturation
% 3.83/0.93  
% 3.83/0.93  % (18501)Memory used [KB]: 8059
% 3.83/0.93  % (18517)Time limit reached!
% 3.83/0.93  % (18517)------------------------------
% 3.83/0.93  % (18517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.93  % (18501)Time elapsed: 0.500 s
% 3.83/0.93  % (18501)------------------------------
% 3.83/0.93  % (18501)------------------------------
% 3.83/0.93  % (18517)Termination reason: Time limit
% 3.83/0.93  
% 3.83/0.93  % (18517)Memory used [KB]: 12792
% 3.83/0.93  % (18517)Time elapsed: 0.507 s
% 3.83/0.93  % (18517)------------------------------
% 3.83/0.93  % (18517)------------------------------
% 3.83/0.94  % (18510)Termination reason: Time limit
% 3.83/0.94  % (18510)Termination phase: Saturation
% 3.83/0.94  
% 3.83/0.94  % (18510)Memory used [KB]: 16886
% 3.83/0.94  % (18510)Time elapsed: 0.500 s
% 3.83/0.94  % (18510)------------------------------
% 3.83/0.94  % (18510)------------------------------
% 4.30/0.97  % (18512)Time limit reached!
% 4.30/0.97  % (18512)------------------------------
% 4.30/0.97  % (18512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.97  % (18512)Termination reason: Time limit
% 4.30/0.97  
% 4.30/0.97  % (18512)Memory used [KB]: 7547
% 4.30/0.97  % (18512)Time elapsed: 0.508 s
% 4.30/0.97  % (18512)------------------------------
% 4.30/0.97  % (18512)------------------------------
% 4.30/0.99  % (18563)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.65/1.03  % (18557)Time limit reached!
% 4.65/1.03  % (18557)------------------------------
% 4.65/1.03  % (18557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.04  % (18558)Time limit reached!
% 4.65/1.04  % (18558)------------------------------
% 4.65/1.04  % (18558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.04  % (18507)Time limit reached!
% 4.65/1.04  % (18507)------------------------------
% 4.65/1.04  % (18507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/1.05  % (18575)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.65/1.05  % (18557)Termination reason: Time limit
% 4.65/1.05  
% 4.65/1.05  % (18557)Memory used [KB]: 6908
% 4.65/1.05  % (18557)Time elapsed: 0.416 s
% 4.65/1.05  % (18557)------------------------------
% 4.65/1.05  % (18557)------------------------------
% 4.65/1.05  % (18576)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.02/1.06  % (18558)Termination reason: Time limit
% 5.02/1.06  % (18507)Termination reason: Time limit
% 5.02/1.06  
% 5.02/1.06  % (18507)Termination phase: Saturation
% 5.02/1.06  
% 5.02/1.06  % (18558)Memory used [KB]: 13432
% 5.02/1.06  % (18507)Memory used [KB]: 10490
% 5.02/1.06  % (18558)Time elapsed: 0.423 s
% 5.02/1.06  % (18507)Time elapsed: 0.600 s
% 5.02/1.06  % (18558)------------------------------
% 5.02/1.06  % (18558)------------------------------
% 5.02/1.06  % (18507)------------------------------
% 5.02/1.06  % (18507)------------------------------
% 5.02/1.07  % (18574)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.02/1.08  % (18593)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.02/1.10  % (18531)Time limit reached!
% 5.02/1.10  % (18531)------------------------------
% 5.02/1.10  % (18531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.10  % (18531)Termination reason: Time limit
% 5.02/1.10  
% 5.02/1.10  % (18531)Memory used [KB]: 7675
% 5.02/1.10  % (18531)Time elapsed: 0.627 s
% 5.02/1.10  % (18531)------------------------------
% 5.02/1.10  % (18531)------------------------------
% 5.02/1.15  % (18516)Time limit reached!
% 5.02/1.15  % (18516)------------------------------
% 5.02/1.15  % (18516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.18/1.16  % (18516)Termination reason: Time limit
% 6.18/1.16  
% 6.18/1.16  % (18516)Memory used [KB]: 14967
% 6.18/1.16  % (18516)Time elapsed: 0.730 s
% 6.18/1.16  % (18516)------------------------------
% 6.18/1.16  % (18516)------------------------------
% 6.18/1.17  % (18629)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.18/1.18  % (18625)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.18/1.18  % (18630)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.55/1.24  % (18661)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.55/1.24  % (18661)Refutation not found, incomplete strategy% (18661)------------------------------
% 6.55/1.24  % (18661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.55/1.24  % (18661)Termination reason: Refutation not found, incomplete strategy
% 6.55/1.24  
% 6.55/1.24  % (18661)Memory used [KB]: 1791
% 6.55/1.24  % (18661)Time elapsed: 0.121 s
% 6.55/1.24  % (18661)------------------------------
% 6.55/1.24  % (18661)------------------------------
% 6.96/1.29  % (18693)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 7.70/1.38  % (18727)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.20/1.59  % (18630)Time limit reached!
% 9.20/1.59  % (18630)------------------------------
% 9.20/1.59  % (18630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.20/1.59  % (18630)Termination reason: Time limit
% 9.20/1.59  
% 9.20/1.59  % (18630)Memory used [KB]: 2686
% 9.20/1.59  % (18630)Time elapsed: 0.512 s
% 9.20/1.59  % (18630)------------------------------
% 9.20/1.59  % (18630)------------------------------
% 9.56/1.62  % (18524)Time limit reached!
% 9.56/1.62  % (18524)------------------------------
% 9.56/1.62  % (18524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.56/1.62  % (18524)Termination reason: Time limit
% 9.56/1.62  
% 9.56/1.62  % (18524)Memory used [KB]: 16502
% 9.56/1.62  % (18524)Time elapsed: 1.222 s
% 9.56/1.62  % (18524)------------------------------
% 9.56/1.62  % (18524)------------------------------
% 9.56/1.65  % (18529)Time limit reached!
% 9.56/1.65  % (18529)------------------------------
% 9.56/1.65  % (18529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.56/1.65  % (18529)Termination reason: Time limit
% 9.56/1.65  % (18529)Termination phase: Saturation
% 9.56/1.65  
% 9.56/1.65  % (18529)Memory used [KB]: 22131
% 9.56/1.65  % (18529)Time elapsed: 1.200 s
% 9.56/1.65  % (18529)------------------------------
% 9.56/1.65  % (18529)------------------------------
% 9.94/1.71  % (18515)Time limit reached!
% 9.94/1.71  % (18515)------------------------------
% 9.94/1.71  % (18515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.94/1.71  % (18515)Termination reason: Time limit
% 9.94/1.71  % (18515)Termination phase: Saturation
% 9.94/1.71  
% 9.94/1.71  % (18515)Memory used [KB]: 12665
% 9.94/1.71  % (18515)Time elapsed: 1.300 s
% 9.94/1.71  % (18515)------------------------------
% 9.94/1.71  % (18515)------------------------------
% 9.94/1.73  % (18801)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 9.94/1.74  % (18802)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 9.94/1.75  % (18526)Refutation found. Thanks to Tanya!
% 9.94/1.75  % SZS status Theorem for theBenchmark
% 9.94/1.75  % SZS output start Proof for theBenchmark
% 10.62/1.75  fof(f9454,plain,(
% 10.62/1.75    $false),
% 10.62/1.75    inference(global_subsumption,[],[f9432,f9436])).
% 10.62/1.75  fof(f9436,plain,(
% 10.62/1.75    r2_hidden(sK4(k9_relat_1(sK3,sK2),k2_relat_1(sK3)),k2_relat_1(sK3))),
% 10.62/1.75    inference(backward_demodulation,[],[f1117,f9389])).
% 10.62/1.75  fof(f9389,plain,(
% 10.62/1.75    k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 10.62/1.75    inference(unit_resulting_resolution,[],[f42,f117,f9033,f95])).
% 10.62/1.75  fof(f95,plain,(
% 10.62/1.75    ( ! [X0,X1] : (k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 10.62/1.75    inference(definition_unfolding,[],[f54,f90,f90])).
% 10.62/1.75  fof(f90,plain,(
% 10.62/1.75    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 10.62/1.75    inference(definition_unfolding,[],[f47,f89])).
% 10.62/1.75  fof(f89,plain,(
% 10.62/1.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 10.62/1.75    inference(definition_unfolding,[],[f50,f88])).
% 10.62/1.75  fof(f88,plain,(
% 10.62/1.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 10.62/1.75    inference(definition_unfolding,[],[f66,f87])).
% 10.62/1.75  fof(f87,plain,(
% 10.62/1.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 10.62/1.75    inference(definition_unfolding,[],[f77,f86])).
% 10.62/1.75  fof(f86,plain,(
% 10.62/1.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 10.62/1.75    inference(definition_unfolding,[],[f82,f85])).
% 10.62/1.75  fof(f85,plain,(
% 10.62/1.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 10.62/1.75    inference(definition_unfolding,[],[f83,f84])).
% 10.62/1.75  fof(f84,plain,(
% 10.62/1.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f10])).
% 10.62/1.75  fof(f10,axiom,(
% 10.62/1.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 10.62/1.75  fof(f83,plain,(
% 10.62/1.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f9])).
% 10.62/1.75  fof(f9,axiom,(
% 10.62/1.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 10.62/1.75  fof(f82,plain,(
% 10.62/1.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f8])).
% 10.62/1.75  fof(f8,axiom,(
% 10.62/1.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 10.62/1.75  fof(f77,plain,(
% 10.62/1.75    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f7])).
% 10.62/1.75  fof(f7,axiom,(
% 10.62/1.75    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 10.62/1.75  fof(f66,plain,(
% 10.62/1.75    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f6])).
% 10.62/1.75  fof(f6,axiom,(
% 10.62/1.75    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 10.62/1.75  fof(f50,plain,(
% 10.62/1.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f5])).
% 10.62/1.75  fof(f5,axiom,(
% 10.62/1.75    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 10.62/1.75  fof(f47,plain,(
% 10.62/1.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f4])).
% 10.62/1.75  fof(f4,axiom,(
% 10.62/1.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 10.62/1.75  fof(f54,plain,(
% 10.62/1.75    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 10.62/1.75    inference(cnf_transformation,[],[f32])).
% 10.62/1.75  fof(f32,plain,(
% 10.62/1.75    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 10.62/1.75    inference(flattening,[],[f31])).
% 10.62/1.75  fof(f31,plain,(
% 10.62/1.75    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 10.62/1.75    inference(ennf_transformation,[],[f15])).
% 10.62/1.75  fof(f15,axiom,(
% 10.62/1.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 10.62/1.75  fof(f9033,plain,(
% 10.62/1.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 10.62/1.75    inference(unit_resulting_resolution,[],[f606,f7844,f57])).
% 10.62/1.75  fof(f57,plain,(
% 10.62/1.75    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 10.62/1.75    inference(cnf_transformation,[],[f2])).
% 10.62/1.75  fof(f2,axiom,(
% 10.62/1.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.62/1.75  fof(f7844,plain,(
% 10.62/1.75    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK3))),
% 10.62/1.75    inference(backward_demodulation,[],[f3609,f7836])).
% 10.62/1.75  fof(f7836,plain,(
% 10.62/1.75    sK0 = sK4(k1_relat_1(sK3),k1_xboole_0)),
% 10.62/1.75    inference(duplicate_literal_removal,[],[f7832])).
% 10.62/1.75  fof(f7832,plain,(
% 10.62/1.75    sK0 = sK4(k1_relat_1(sK3),k1_xboole_0) | sK0 = sK4(k1_relat_1(sK3),k1_xboole_0)),
% 10.62/1.75    inference(resolution,[],[f7806,f72])).
% 10.62/1.75  fof(f72,plain,(
% 10.62/1.75    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 10.62/1.75    inference(cnf_transformation,[],[f3])).
% 10.62/1.75  fof(f3,axiom,(
% 10.62/1.75    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 10.62/1.75  fof(f7806,plain,(
% 10.62/1.75    sP6(sK4(k1_relat_1(sK3),k1_xboole_0),sK0,sK0)),
% 10.62/1.75    inference(unit_resulting_resolution,[],[f3414,f606,f1120])).
% 10.62/1.75  fof(f1120,plain,(
% 10.62/1.75    ( ! [X6,X8,X7,X9] : (~r1_tarski(X6,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)) | r1_tarski(X6,X9) | sP6(sK4(X6,X9),X8,X7)) )),
% 10.62/1.75    inference(resolution,[],[f157,f104])).
% 10.62/1.75  fof(f104,plain,(
% 10.62/1.75    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | sP6(X3,X1,X0)) )),
% 10.62/1.75    inference(equality_resolution,[],[f98])).
% 10.62/1.75  fof(f98,plain,(
% 10.62/1.75    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 10.62/1.75    inference(definition_unfolding,[],[f74,f89])).
% 10.62/1.75  fof(f74,plain,(
% 10.62/1.75    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 10.62/1.75    inference(cnf_transformation,[],[f3])).
% 10.62/1.75  fof(f157,plain,(
% 10.62/1.75    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 10.62/1.75    inference(resolution,[],[f58,f59])).
% 10.62/1.75  fof(f59,plain,(
% 10.62/1.75    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f33])).
% 10.62/1.75  fof(f33,plain,(
% 10.62/1.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 10.62/1.75    inference(ennf_transformation,[],[f1])).
% 10.62/1.75  fof(f1,axiom,(
% 10.62/1.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 10.62/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 10.62/1.75  fof(f58,plain,(
% 10.62/1.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 10.62/1.75    inference(cnf_transformation,[],[f33])).
% 10.62/1.76  fof(f3414,plain,(
% 10.62/1.76    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f3393,f568])).
% 10.62/1.76  fof(f568,plain,(
% 10.62/1.76    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 10.62/1.76    inference(superposition,[],[f446,f103])).
% 10.62/1.76  fof(f103,plain,(
% 10.62/1.76    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 10.62/1.76    inference(equality_resolution,[],[f64])).
% 10.62/1.76  fof(f64,plain,(
% 10.62/1.76    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 10.62/1.76    inference(cnf_transformation,[],[f11])).
% 10.62/1.76  fof(f11,axiom,(
% 10.62/1.76    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 10.62/1.76  fof(f446,plain,(
% 10.62/1.76    ( ! [X19] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,sK1))) | ~r1_tarski(k1_relat_1(sK3),X19)) )),
% 10.62/1.76    inference(resolution,[],[f80,f92])).
% 10.62/1.76  fof(f92,plain,(
% 10.62/1.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 10.62/1.76    inference(definition_unfolding,[],[f44,f90])).
% 10.62/1.76  fof(f44,plain,(
% 10.62/1.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 10.62/1.76    inference(cnf_transformation,[],[f26])).
% 10.62/1.76  fof(f26,plain,(
% 10.62/1.76    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 10.62/1.76    inference(flattening,[],[f25])).
% 10.62/1.76  fof(f25,plain,(
% 10.62/1.76    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 10.62/1.76    inference(ennf_transformation,[],[f24])).
% 10.62/1.76  fof(f24,negated_conjecture,(
% 10.62/1.76    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 10.62/1.76    inference(negated_conjecture,[],[f23])).
% 10.62/1.76  fof(f23,conjecture,(
% 10.62/1.76    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 10.62/1.76  fof(f80,plain,(
% 10.62/1.76    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 10.62/1.76    inference(cnf_transformation,[],[f39])).
% 10.62/1.76  fof(f39,plain,(
% 10.62/1.76    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 10.62/1.76    inference(flattening,[],[f38])).
% 10.62/1.76  fof(f38,plain,(
% 10.62/1.76    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 10.62/1.76    inference(ennf_transformation,[],[f20])).
% 10.62/1.76  fof(f20,axiom,(
% 10.62/1.76    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 10.62/1.76  fof(f3393,plain,(
% 10.62/1.76    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f310,f1891])).
% 10.62/1.76  fof(f1891,plain,(
% 10.62/1.76    ( ! [X4,X5,X3] : (m1_subset_1(k9_relat_1(X4,X5),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) )),
% 10.62/1.76    inference(superposition,[],[f299,f103])).
% 10.62/1.76  fof(f299,plain,(
% 10.62/1.76    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1))) )),
% 10.62/1.76    inference(duplicate_literal_removal,[],[f298])).
% 10.62/1.76  fof(f298,plain,(
% 10.62/1.76    ( ! [X2,X0,X3,X1] : (m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.62/1.76    inference(superposition,[],[f78,f79])).
% 10.62/1.76  fof(f79,plain,(
% 10.62/1.76    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.62/1.76    inference(cnf_transformation,[],[f37])).
% 10.62/1.76  fof(f37,plain,(
% 10.62/1.76    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.62/1.76    inference(ennf_transformation,[],[f19])).
% 10.62/1.76  fof(f19,axiom,(
% 10.62/1.76    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 10.62/1.76  fof(f78,plain,(
% 10.62/1.76    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.62/1.76    inference(cnf_transformation,[],[f36])).
% 10.62/1.76  fof(f36,plain,(
% 10.62/1.76    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.62/1.76    inference(ennf_transformation,[],[f18])).
% 10.62/1.76  fof(f18,axiom,(
% 10.62/1.76    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 10.62/1.76  fof(f310,plain,(
% 10.62/1.76    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f302,f62])).
% 10.62/1.76  fof(f62,plain,(
% 10.62/1.76    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 10.62/1.76    inference(cnf_transformation,[],[f13])).
% 10.62/1.76  fof(f13,axiom,(
% 10.62/1.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 10.62/1.76  fof(f302,plain,(
% 10.62/1.76    ~r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 10.62/1.76    inference(backward_demodulation,[],[f91,f295])).
% 10.62/1.76  fof(f295,plain,(
% 10.62/1.76    ( ! [X0] : (k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f92,f79])).
% 10.62/1.76  fof(f91,plain,(
% 10.62/1.76    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 10.62/1.76    inference(definition_unfolding,[],[f46,f90,f90])).
% 10.62/1.76  fof(f46,plain,(
% 10.62/1.76    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 10.62/1.76    inference(cnf_transformation,[],[f26])).
% 10.62/1.76  fof(f3609,plain,(
% 10.62/1.76    r1_tarski(k6_enumset1(sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0),sK4(k1_relat_1(sK3),k1_xboole_0)),k1_relat_1(sK3))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f3443,f319])).
% 10.62/1.76  fof(f319,plain,(
% 10.62/1.76    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 10.62/1.76    inference(resolution,[],[f94,f62])).
% 10.62/1.76  fof(f94,plain,(
% 10.62/1.76    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 10.62/1.76    inference(definition_unfolding,[],[f53,f90])).
% 10.62/1.76  fof(f53,plain,(
% 10.62/1.76    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 10.62/1.76    inference(cnf_transformation,[],[f30])).
% 10.62/1.76  fof(f30,plain,(
% 10.62/1.76    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 10.62/1.76    inference(ennf_transformation,[],[f12])).
% 10.62/1.76  fof(f12,axiom,(
% 10.62/1.76    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 10.62/1.76  fof(f3443,plain,(
% 10.62/1.76    r2_hidden(sK4(k1_relat_1(sK3),k1_xboole_0),k1_relat_1(sK3))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f3414,f59])).
% 10.62/1.76  fof(f606,plain,(
% 10.62/1.76    r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f117,f158,f52])).
% 10.62/1.76  fof(f52,plain,(
% 10.62/1.76    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 10.62/1.76    inference(cnf_transformation,[],[f29])).
% 10.62/1.76  fof(f29,plain,(
% 10.62/1.76    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 10.62/1.76    inference(ennf_transformation,[],[f14])).
% 10.62/1.76  fof(f14,axiom,(
% 10.62/1.76    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 10.62/1.76  fof(f158,plain,(
% 10.62/1.76    v4_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f92,f68])).
% 10.62/1.76  fof(f68,plain,(
% 10.62/1.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 10.62/1.76    inference(cnf_transformation,[],[f35])).
% 10.62/1.76  fof(f35,plain,(
% 10.62/1.76    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.62/1.76    inference(ennf_transformation,[],[f17])).
% 10.62/1.76  fof(f17,axiom,(
% 10.62/1.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 10.62/1.76  fof(f117,plain,(
% 10.62/1.76    v1_relat_1(sK3)),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f92,f67])).
% 10.62/1.76  fof(f67,plain,(
% 10.62/1.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 10.62/1.76    inference(cnf_transformation,[],[f34])).
% 10.62/1.76  fof(f34,plain,(
% 10.62/1.76    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.62/1.76    inference(ennf_transformation,[],[f16])).
% 10.62/1.76  fof(f16,axiom,(
% 10.62/1.76    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 10.62/1.76  fof(f42,plain,(
% 10.62/1.76    v1_funct_1(sK3)),
% 10.62/1.76    inference(cnf_transformation,[],[f26])).
% 10.62/1.76  fof(f1117,plain,(
% 10.62/1.76    r2_hidden(sK4(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k2_relat_1(sK3))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f302,f315,f157])).
% 10.62/1.76  fof(f315,plain,(
% 10.62/1.76    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f301,f62])).
% 10.62/1.76  fof(f301,plain,(
% 10.62/1.76    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(k2_relat_1(sK3)))) )),
% 10.62/1.76    inference(backward_demodulation,[],[f286,f296])).
% 10.62/1.76  fof(f296,plain,(
% 10.62/1.76    ( ! [X0] : (k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0) = k9_relat_1(sK3,X0)) )),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f229,f79])).
% 10.62/1.76  fof(f229,plain,(
% 10.62/1.76    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f117,f42,f49])).
% 10.62/1.76  fof(f49,plain,(
% 10.62/1.76    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 10.62/1.76    inference(cnf_transformation,[],[f28])).
% 10.62/1.76  fof(f28,plain,(
% 10.62/1.76    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.62/1.76    inference(flattening,[],[f27])).
% 10.62/1.76  fof(f27,plain,(
% 10.62/1.76    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 10.62/1.76    inference(ennf_transformation,[],[f21])).
% 10.62/1.76  fof(f21,axiom,(
% 10.62/1.76    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 10.62/1.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 10.62/1.76  fof(f286,plain,(
% 10.62/1.76    ( ! [X0] : (m1_subset_1(k7_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3,X0),k1_zfmisc_1(k2_relat_1(sK3)))) )),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f229,f78])).
% 10.62/1.76  fof(f9432,plain,(
% 10.62/1.76    ~r2_hidden(sK4(k9_relat_1(sK3,sK2),k2_relat_1(sK3)),k2_relat_1(sK3))),
% 10.62/1.76    inference(backward_demodulation,[],[f308,f9389])).
% 10.62/1.76  fof(f308,plain,(
% 10.62/1.76    ~r2_hidden(sK4(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 10.62/1.76    inference(unit_resulting_resolution,[],[f302,f60])).
% 10.62/1.76  fof(f60,plain,(
% 10.62/1.76    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 10.62/1.76    inference(cnf_transformation,[],[f33])).
% 10.62/1.76  % SZS output end Proof for theBenchmark
% 10.62/1.76  % (18526)------------------------------
% 10.62/1.76  % (18526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.62/1.76  % (18526)Termination reason: Refutation
% 10.62/1.76  
% 10.62/1.76  % (18526)Memory used [KB]: 26609
% 10.62/1.76  % (18526)Time elapsed: 1.301 s
% 10.62/1.76  % (18526)------------------------------
% 10.62/1.76  % (18526)------------------------------
% 10.62/1.76  % (18497)Success in time 1.39 s
%------------------------------------------------------------------------------
