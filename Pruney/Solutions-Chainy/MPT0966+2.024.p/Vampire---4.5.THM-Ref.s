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
% DateTime   : Thu Dec  3 13:00:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 (104658 expanded)
%              Number of leaves         :   13 (21782 expanded)
%              Depth                    :   42
%              Number of atoms          :  361 (472283 expanded)
%              Number of equality atoms :  152 (103572 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f605,plain,(
    $false ),
    inference(subsumption_resolution,[],[f602,f472])).

fof(f472,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f440,f464])).

fof(f464,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f463,f442])).

fof(f442,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f413,f421])).

fof(f421,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f420,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f420,plain,(
    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f419,f333])).

fof(f333,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f329,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f329,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f328,f250])).

fof(f250,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f249,f221])).

fof(f221,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f146,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f149,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f149,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f147,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f147,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f143,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f143,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f119,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f121,f96])).

fof(f96,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f74,f72])).

fof(f72,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f121,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f70,f113,f120])).

fof(f120,plain,
    ( sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(forward_demodulation,[],[f117,f115])).

fof(f115,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f113,f52])).

fof(f117,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f89,f79])).

fof(f79,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(backward_demodulation,[],[f34,f75])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f34,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f86,f80])).

fof(f80,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f77,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f77,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f33,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f84,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f83,f80])).

fof(f83,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f73,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f33,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f70,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f29,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f140,f61])).

fof(f140,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f113,f134])).

fof(f249,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f144,f150])).

fof(f144,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f135,f61])).

fof(f135,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f70,f134])).

fof(f328,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f320,f30])).

fof(f320,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(resolution,[],[f275,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f275,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f213,f150])).

fof(f213,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f204,f47])).

fof(f204,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f89,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f138,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f82,f134])).

fof(f82,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f79,f40])).

fof(f419,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f418,f47])).

fof(f418,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f346,f62])).

fof(f346,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f91,f333])).

fof(f91,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f78,f40])).

fof(f78,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f50])).

fof(f413,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f412,f333])).

fof(f412,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f344,f47])).

fof(f344,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f88,f333])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | sK0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f84,f40])).

fof(f463,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f357,f421])).

fof(f357,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f121,f333])).

fof(f440,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f410,f421])).

fof(f410,plain,(
    ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f409,f407])).

fof(f407,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f335,f62])).

fof(f335,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f33,f333])).

fof(f409,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f408,f62])).

fof(f408,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f336,f333])).

fof(f336,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f70,f333])).

fof(f602,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f435,f597])).

fof(f597,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f593,f472])).

fof(f593,plain,(
    ! [X8] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X8)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f586,f546])).

fof(f546,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f545,f442])).

fof(f545,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f397,f421])).

fof(f397,plain,(
    ! [X0] :
      ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,X0,sK3)
      | k1_xboole_0 = sK1 ) ),
    inference(backward_demodulation,[],[f268,f333])).

fof(f268,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_relat_1(sK3) = k1_relset_1(sK0,X0,sK3) ) ),
    inference(resolution,[],[f213,f52])).

fof(f586,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X8,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X8) ) ),
    inference(resolution,[],[f489,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f489,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f485,f47])).

fof(f485,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(backward_demodulation,[],[f453,f480])).

fof(f480,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f479,f464])).

fof(f479,plain,(
    sK2 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f473,f47])).

fof(f473,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | sK2 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f444,f464])).

fof(f444,plain,
    ( sK2 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK2,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f426,f421])).

fof(f426,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(k1_xboole_0))
    | sK2 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f82,f421])).

fof(f453,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X2)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f452,f421])).

fof(f452,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f451,f421])).

fof(f451,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f351,f47])).

fof(f351,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(backward_demodulation,[],[f103,f333])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f101,f80])).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f48,f96])).

fof(f435,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f334,f421])).

fof(f334,plain,(
    v1_funct_2(sK3,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f32,f333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (26172)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (26163)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (26153)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (26153)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (26162)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (26149)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f605,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f602,f472])).
% 0.21/0.55  fof(f472,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f440,f464])).
% 0.21/0.55  fof(f464,plain,(
% 0.21/0.55    k1_xboole_0 = sK2),
% 0.21/0.55    inference(subsumption_resolution,[],[f463,f442])).
% 0.21/0.55  fof(f442,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f413,f421])).
% 0.21/0.55  fof(f421,plain,(
% 0.21/0.55    k1_xboole_0 = sK3),
% 0.21/0.55    inference(forward_demodulation,[],[f420,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.55  fof(f420,plain,(
% 0.21/0.55    sK3 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f419,f333])).
% 0.21/0.55  fof(f333,plain,(
% 0.21/0.55    k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f329,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f15])).
% 0.21/0.55  fof(f15,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.55  fof(f329,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(resolution,[],[f328,f250])).
% 0.21/0.55  fof(f250,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(subsumption_resolution,[],[f249,f221])).
% 0.21/0.55  fof(f221,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.55  fof(f220,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f146,f150])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(subsumption_resolution,[],[f149,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3),
% 0.21/0.55    inference(resolution,[],[f147,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(forward_demodulation,[],[f143,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f119,f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    sK0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f121,f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f74,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(subsumption_resolution,[],[f71,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    inference(resolution,[],[f32,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f33,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(global_subsumption,[],[f70,f113,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    sK0 != k1_relat_1(sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f117,f115])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 0.21/0.55    inference(resolution,[],[f113,f52])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.55    inference(resolution,[],[f113,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.55    inference(resolution,[],[f89,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f34,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f33,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f86,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    v1_relat_1(sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f77,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f33,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 0.21/0.55    inference(resolution,[],[f84,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f83,f80])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f73,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    v4_relat_1(sK3,sK0)),
% 0.21/0.55    inference(resolution,[],[f33,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f29,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    v1_funct_1(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.21/0.55    inference(resolution,[],[f113,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(forward_demodulation,[],[f140,f61])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f113,f134])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f248])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f144,f150])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(forward_demodulation,[],[f135,f61])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f70,f134])).
% 0.21/0.55  fof(f328,plain,(
% 0.21/0.55    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f320,f30])).
% 0.21/0.55  fof(f320,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.55    inference(resolution,[],[f275,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f273])).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(superposition,[],[f213,f150])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f204,f47])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(superposition,[],[f89,f145])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(subsumption_resolution,[],[f138,f47])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k2_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(superposition,[],[f82,f134])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f79,f40])).
% 0.21/0.55  fof(f419,plain,(
% 0.21/0.55    sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f418,f47])).
% 0.21/0.55  fof(f418,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f346,f62])).
% 0.21/0.55  fof(f346,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f91,f333])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f78,f40])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.55    inference(resolution,[],[f33,f50])).
% 0.21/0.55  fof(f413,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.55    inference(forward_demodulation,[],[f412,f333])).
% 0.21/0.55  fof(f412,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f344,f47])).
% 0.21/0.55  fof(f344,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 0.21/0.55    inference(backward_demodulation,[],[f88,f333])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ~r1_tarski(sK0,k1_relat_1(sK3)) | sK0 = k1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f84,f40])).
% 0.21/0.55  fof(f463,plain,(
% 0.21/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(forward_demodulation,[],[f357,f421])).
% 0.21/0.55  fof(f357,plain,(
% 0.21/0.55    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(backward_demodulation,[],[f121,f333])).
% 0.21/0.55  fof(f440,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f410,f421])).
% 0.21/0.55  fof(f410,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f409,f407])).
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.55    inference(forward_demodulation,[],[f335,f62])).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.55    inference(backward_demodulation,[],[f33,f333])).
% 0.21/0.55  fof(f409,plain,(
% 0.21/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f408,f62])).
% 0.21/0.55  fof(f408,plain,(
% 0.21/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f336,f333])).
% 0.21/0.55  fof(f336,plain,(
% 0.21/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.55    inference(backward_demodulation,[],[f70,f333])).
% 0.21/0.55  fof(f602,plain,(
% 0.21/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f435,f597])).
% 0.21/0.55  fof(f597,plain,(
% 0.21/0.55    k1_xboole_0 = sK1),
% 0.21/0.55    inference(resolution,[],[f593,f472])).
% 0.21/0.55  fof(f593,plain,(
% 0.21/0.55    ( ! [X8] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X8) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f586,f546])).
% 0.21/0.55  fof(f546,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(forward_demodulation,[],[f545,f442])).
% 0.21/0.55  fof(f545,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(forward_demodulation,[],[f397,f421])).
% 0.21/0.55  fof(f397,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,X0,sK3) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(backward_demodulation,[],[f268,f333])).
% 0.21/0.55  fof(f268,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | k1_relat_1(sK3) = k1_relset_1(sK0,X0,sK3)) )),
% 0.21/0.55    inference(resolution,[],[f213,f52])).
% 0.21/0.55  fof(f586,plain,(
% 0.21/0.55    ( ! [X8] : (k1_xboole_0 = sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,X8,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X8)) )),
% 0.21/0.55    inference(resolution,[],[f489,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f489,plain,(
% 0.21/0.55    ( ! [X2,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f485,f47])).
% 0.21/0.55  fof(f485,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,X2) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(backward_demodulation,[],[f453,f480])).
% 0.21/0.55  fof(f480,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f479,f464])).
% 0.21/0.55  fof(f479,plain,(
% 0.21/0.55    sK2 = k2_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f473,f47])).
% 0.21/0.55  fof(f473,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | sK2 = k2_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f444,f464])).
% 0.21/0.55  fof(f444,plain,(
% 0.21/0.55    sK2 = k2_relat_1(k1_xboole_0) | ~r1_tarski(sK2,k2_relat_1(k1_xboole_0))),
% 0.21/0.55    inference(forward_demodulation,[],[f426,f421])).
% 0.21/0.55  fof(f426,plain,(
% 0.21/0.55    ~r1_tarski(sK2,k2_relat_1(k1_xboole_0)) | sK2 = k2_relat_1(sK3)),
% 0.21/0.55    inference(backward_demodulation,[],[f82,f421])).
% 0.21/0.55  fof(f453,plain,(
% 0.21/0.55    ( ! [X2,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relat_1(k1_xboole_0),X2) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(forward_demodulation,[],[f452,f421])).
% 0.21/0.55  fof(f452,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k1_xboole_0),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(forward_demodulation,[],[f451,f421])).
% 0.21/0.55  fof(f451,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f351,f47])).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,X1) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(backward_demodulation,[],[f103,f333])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f101,f80])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = sK1) )),
% 0.21/0.55    inference(superposition,[],[f48,f96])).
% 0.21/0.55  fof(f435,plain,(
% 0.21/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f334,f421])).
% 0.21/0.55  fof(f334,plain,(
% 0.21/0.55    v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f32,f333])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (26153)------------------------------
% 0.21/0.55  % (26153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26153)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (26153)Memory used [KB]: 6396
% 0.21/0.55  % (26153)Time elapsed: 0.086 s
% 0.21/0.55  % (26153)------------------------------
% 0.21/0.55  % (26153)------------------------------
% 0.21/0.55  % (26144)Success in time 0.188 s
%------------------------------------------------------------------------------
