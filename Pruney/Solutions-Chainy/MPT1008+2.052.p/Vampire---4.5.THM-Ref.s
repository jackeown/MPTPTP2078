%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 624 expanded)
%              Number of leaves         :   18 ( 178 expanded)
%              Depth                    :   26
%              Number of atoms          :  278 (1290 expanded)
%              Number of equality atoms :  132 ( 737 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(subsumption_resolution,[],[f275,f240])).

fof(f240,plain,(
    o_0_0_xboole_0 != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f232,f77])).

fof(f77,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f44,f42,f42])).

fof(f42,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f232,plain,(
    k2_relat_1(o_0_0_xboole_0) != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f127,f224])).

fof(f224,plain,(
    o_0_0_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2 ),
    inference(superposition,[],[f111,f216])).

fof(f216,plain,(
    o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f215,f127])).

fof(f215,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f214,f98])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f39,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f214,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f211])).

fof(f211,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f159,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f159,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | k1_relat_1(sK2) != k1_relat_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = k2_enumset1(k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0))
      | o_0_0_xboole_0 = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f85,f145])).

fof(f145,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f90,f107])).

fof(f107,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f106,f98])).

fof(f106,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f105,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f64,f75])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f42,f72,f72,f71,f71])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f55,f72,f72])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f111,plain,
    ( o_0_0_xboole_0 != k1_relat_1(sK2)
    | o_0_0_xboole_0 = sK2 ),
    inference(resolution,[],[f81,f98])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | o_0_0_xboole_0 != k1_relat_1(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f42,f42])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f127,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f73,f126])).

fof(f126,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f63,f75])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f41,f72,f72])).

fof(f41,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f275,plain,(
    o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f274,f77])).

fof(f274,plain,(
    k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f273,f119])).

fof(f119,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[],[f58,f114])).

fof(f114,plain,(
    ! [X0] : o_0_0_xboole_0 = sK4(o_0_0_xboole_0,X0) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = sK4(X0,X1) ) ),
    inference(superposition,[],[f110,f60])).

fof(f60,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != k1_relat_1(sK4(X0,X1))
      | o_0_0_xboole_0 = sK4(X0,X1) ) ),
    inference(resolution,[],[f81,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f273,plain,
    ( ~ v1_relat_1(o_0_0_xboole_0)
    | k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f271,f78])).

fof(f78,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f43,f42,f42])).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f271,plain,
    ( o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    inference(resolution,[],[f265,f118])).

fof(f118,plain,(
    v1_funct_1(o_0_0_xboole_0) ),
    inference(superposition,[],[f59,f114])).

fof(f59,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f265,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | o_0_0_xboole_0 != k1_relat_1(X3)
      | ~ v1_relat_1(X3)
      | k2_relat_1(X3) = k2_enumset1(k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0)) ) ),
    inference(superposition,[],[f85,f246])).

fof(f246,plain,(
    o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f245,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f245,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f236,f77])).

fof(f236,plain,
    ( ~ r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f136,f224])).

fof(f136,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f134,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f134,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relat_1(sK2))
    | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f133,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f132,f126])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f131,f74])).

fof(f74,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | o_0_0_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f130,f37])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | o_0_0_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f129,f76])).

fof(f76,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f38,f72])).

fof(f38,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | o_0_0_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(resolution,[],[f91,f75])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(definition_unfolding,[],[f70,f42])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28238)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28239)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (28237)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (28246)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (28247)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (28246)Refutation not found, incomplete strategy% (28246)------------------------------
% 0.21/0.53  % (28246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28246)Memory used [KB]: 10618
% 0.21/0.53  % (28246)Time elapsed: 0.106 s
% 0.21/0.53  % (28246)------------------------------
% 0.21/0.53  % (28246)------------------------------
% 0.21/0.53  % (28236)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (28251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (28258)Refutation not found, incomplete strategy% (28258)------------------------------
% 0.21/0.53  % (28258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28258)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28258)Memory used [KB]: 10746
% 0.21/0.53  % (28258)Time elapsed: 0.115 s
% 0.21/0.53  % (28258)------------------------------
% 0.21/0.53  % (28258)------------------------------
% 0.21/0.53  % (28242)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28264)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (28242)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f275,f240])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    o_0_0_xboole_0 != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f232,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.54    inference(definition_unfolding,[],[f44,f42,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    k2_relat_1(o_0_0_xboole_0) != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.54    inference(backward_demodulation,[],[f127,f224])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    o_0_0_xboole_0 = sK2),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f223])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    o_0_0_xboole_0 != o_0_0_xboole_0 | o_0_0_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f111,f216])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f127])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f214,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f62,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f52,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.54    inference(negated_conjecture,[],[f18])).
% 0.21/0.54  fof(f18,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f159,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X3] : (~v1_funct_1(X3) | k1_relat_1(sK2) != k1_relat_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = k2_enumset1(k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0)) | o_0_0_xboole_0 = k1_relat_1(sK2)) )),
% 0.21/0.54    inference(superposition,[],[f85,f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f90,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f106,f98])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f105,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(resolution,[],[f64,f75])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | o_0_0_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f65,f42,f72,f72,f71,f71])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f55,f72,f72])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    o_0_0_xboole_0 != k1_relat_1(sK2) | o_0_0_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f81,f98])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | o_0_0_xboole_0 != k1_relat_1(X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f47,f42,f42])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.21/0.54    inference(backward_demodulation,[],[f73,f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f63,f75])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.54    inference(definition_unfolding,[],[f41,f72,f72])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f274,f77])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f273,f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    v1_relat_1(o_0_0_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f58,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0] : (o_0_0_xboole_0 = sK4(o_0_0_xboole_0,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X0,X1] : (o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK4(X0,X1)) )),
% 0.21/0.54    inference(superposition,[],[f110,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0,X1] : (o_0_0_xboole_0 != k1_relat_1(sK4(X0,X1)) | o_0_0_xboole_0 = sK4(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f81,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    ~v1_relat_1(o_0_0_xboole_0) | k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f271,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.21/0.54    inference(definition_unfolding,[],[f43,f42,f42])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.54    inference(resolution,[],[f265,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    v1_funct_1(o_0_0_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f59,f114])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    ( ! [X3] : (~v1_funct_1(X3) | o_0_0_xboole_0 != k1_relat_1(X3) | ~v1_relat_1(X3) | k2_relat_1(X3) = k2_enumset1(k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0),k1_funct_1(X3,sK0))) )),
% 0.21/0.54    inference(superposition,[],[f85,f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f245,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f45,f42])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    ~r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f236,f77])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(o_0_0_xboole_0),k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f136,f224])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.54    inference(resolution,[],[f134,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relat_1(sK2)) | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.54    inference(resolution,[],[f133,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f51,f42])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f132,f126])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f131,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    o_0_0_xboole_0 != sK1),
% 0.21/0.54    inference(definition_unfolding,[],[f40,f42])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | o_0_0_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f37])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | o_0_0_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f129,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f72])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | o_0_0_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 0.21/0.54    inference(resolution,[],[f91,f75])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | o_0_0_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f70,f42])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (28242)------------------------------
% 0.21/0.54  % (28242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28242)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (28242)Memory used [KB]: 6396
% 0.21/0.54  % (28242)Time elapsed: 0.119 s
% 0.21/0.54  % (28242)------------------------------
% 0.21/0.54  % (28242)------------------------------
% 0.21/0.54  % (28235)Success in time 0.174 s
%------------------------------------------------------------------------------
