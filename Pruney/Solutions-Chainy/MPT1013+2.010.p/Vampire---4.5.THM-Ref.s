%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 231 expanded)
%              Number of leaves         :    9 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 (1001 expanded)
%              Number of equality atoms :   70 ( 584 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(global_subsumption,[],[f58,f154])).

fof(f154,plain,(
    sK0 = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f153,f42])).

fof(f42,plain,(
    sK0 = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f41,f24])).

fof(f24,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    & sK0 = k2_relset_1(sK0,sK0,sK2)
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
            & k2_relset_1(X0,X0,X2) = X0
            & k2_relset_1(X0,X0,X1) = X0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1))
          & sK0 = k2_relset_1(sK0,sK0,X2)
          & sK0 = k2_relset_1(sK0,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1))
        & sK0 = k2_relset_1(sK0,sK0,X2)
        & sK0 = k2_relset_1(sK0,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
   => ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
      & sK0 = k2_relset_1(sK0,sK0,sK2)
      & sK0 = k2_relset_1(sK0,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

fof(f41,plain,(
    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f39,f37])).

fof(f37,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f39,plain,(
    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) ),
    inference(resolution,[],[f29,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f153,plain,(
    k9_relat_1(sK1,sK0) = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f152,f44])).

fof(f44,plain,(
    sK0 = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f43,f25])).

fof(f25,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f40,f38])).

fof(f38,plain,(
    ! [X1] : k7_relset_1(sK0,sK0,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0) ),
    inference(resolution,[],[f29,f23])).

fof(f152,plain,(
    k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f151,f118])).

fof(f118,plain,(
    ! [X0] : k9_relat_1(sK1,k9_relat_1(sK2,X0)) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0) ),
    inference(forward_demodulation,[],[f117,f99])).

fof(f99,plain,(
    ! [X9] : k9_relat_1(k5_relat_1(sK2,sK1),X9) = k9_relat_1(sK1,k9_relat_1(sK2,X9)) ),
    inference(resolution,[],[f36,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f28,f22])).

fof(f117,plain,(
    ! [X0] : k9_relat_1(k5_relat_1(sK2,sK1),X0) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0) ),
    inference(forward_demodulation,[],[f114,f56])).

fof(f56,plain,(
    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f47,f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relset_1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ) ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f114,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),X0) = k9_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),X0) ),
    inference(resolution,[],[f64,f22])).

fof(f64,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k7_relset_1(sK0,X6,k4_relset_1(sK0,sK0,X5,X6,sK2,X4),X7) = k9_relat_1(k4_relset_1(sK0,sK0,X5,X6,sK2,X4),X7) ) ),
    inference(resolution,[],[f52,f23])).

fof(f52,plain,(
    ! [X26,X24,X23,X21,X27,X25,X22] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k7_relset_1(X25,X23,k4_relset_1(X25,X26,X22,X23,X24,X21),X27) = k9_relat_1(k4_relset_1(X25,X26,X22,X23,X24,X21),X27) ) ),
    inference(resolution,[],[f33,f31])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f151,plain,(
    k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK0) ),
    inference(forward_demodulation,[],[f148,f56])).

fof(f148,plain,(
    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k7_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),sK0) ),
    inference(resolution,[],[f76,f22])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k7_relset_1(sK0,X5,k4_relset_1(sK0,sK0,X4,X5,sK2,X3),sK0) = k2_relset_1(sK0,X5,k4_relset_1(sK0,sK0,X4,X5,sK2,X3)) ) ),
    inference(resolution,[],[f51,f23])).

fof(f51,plain,(
    ! [X19,X17,X15,X20,X18,X16] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k7_relset_1(X19,X17,k4_relset_1(X19,X20,X16,X17,X18,X15),X19) = k2_relset_1(X19,X17,k4_relset_1(X19,X20,X16,X17,X18,X15)) ) ),
    inference(resolution,[],[f33,f29])).

fof(f58,plain,(
    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f26,f56])).

fof(f26,plain,(
    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:06:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (3268)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.41  % (3270)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.42  % (3263)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (3270)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f155,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(global_subsumption,[],[f58,f154])).
% 0.20/0.42  fof(f154,plain,(
% 0.20/0.42    sK0 = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 0.20/0.42    inference(forward_demodulation,[],[f153,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    sK0 = k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(forward_demodulation,[],[f41,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) & sK0 = k2_relset_1(sK0,sK0,sK2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) & sK0 = k2_relset_1(sK0,sK0,X2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ? [X2] : (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) & sK0 = k2_relset_1(sK0,sK0,X2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) => (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) & sK0 = k2_relset_1(sK0,sK0,sK2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.20/0.42    inference(flattening,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)),
% 0.20/0.42    inference(forward_demodulation,[],[f39,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)) )),
% 0.20/0.43    inference(resolution,[],[f31,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)),
% 0.20/0.43    inference(resolution,[],[f29,f22])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    k9_relat_1(sK1,sK0) = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 0.20/0.43    inference(forward_demodulation,[],[f152,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    sK0 = k9_relat_1(sK2,sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f43,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f40,f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X1] : (k7_relset_1(sK0,sK0,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 0.20/0.43    inference(resolution,[],[f31,f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0)),
% 0.20/0.43    inference(resolution,[],[f29,f23])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k9_relat_1(sK2,sK0))),
% 0.20/0.43    inference(forward_demodulation,[],[f151,f118])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK2,X0)) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f117,f99])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    ( ! [X9] : (k9_relat_1(k5_relat_1(sK2,sK1),X9) = k9_relat_1(sK1,k9_relat_1(sK2,X9))) )),
% 0.20/0.43    inference(resolution,[],[f36,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    v1_relat_1(sK2)),
% 0.20/0.43    inference(resolution,[],[f28,f23])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1))) )),
% 0.20/0.43    inference(resolution,[],[f34,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    v1_relat_1(sK1)),
% 0.20/0.43    inference(resolution,[],[f28,f22])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ( ! [X0] : (k9_relat_1(k5_relat_1(sK2,sK1),X0) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f114,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 0.20/0.43    inference(resolution,[],[f47,f23])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k4_relset_1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)) )),
% 0.20/0.43    inference(resolution,[],[f32,f22])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),X0) = k9_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),X0)) )),
% 0.20/0.43    inference(resolution,[],[f64,f22])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k7_relset_1(sK0,X6,k4_relset_1(sK0,sK0,X5,X6,sK2,X4),X7) = k9_relat_1(k4_relset_1(sK0,sK0,X5,X6,sK2,X4),X7)) )),
% 0.20/0.43    inference(resolution,[],[f52,f23])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X26,X24,X23,X21,X27,X25,X22] : (~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k7_relset_1(X25,X23,k4_relset_1(X25,X26,X22,X23,X24,X21),X27) = k9_relat_1(k4_relset_1(X25,X26,X22,X23,X24,X21),X27)) )),
% 0.20/0.43    inference(resolution,[],[f33,f31])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f148,f56])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k7_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),sK0)),
% 0.20/0.43    inference(resolution,[],[f76,f22])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k7_relset_1(sK0,X5,k4_relset_1(sK0,sK0,X4,X5,sK2,X3),sK0) = k2_relset_1(sK0,X5,k4_relset_1(sK0,sK0,X4,X5,sK2,X3))) )),
% 0.20/0.43    inference(resolution,[],[f51,f23])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X19,X17,X15,X20,X18,X16] : (~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) | k7_relset_1(X19,X17,k4_relset_1(X19,X20,X16,X17,X18,X15),X19) = k2_relset_1(X19,X17,k4_relset_1(X19,X20,X16,X17,X18,X15))) )),
% 0.20/0.43    inference(resolution,[],[f33,f29])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 0.20/0.43    inference(backward_demodulation,[],[f26,f56])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (3270)------------------------------
% 0.20/0.43  % (3270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (3270)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (3270)Memory used [KB]: 10874
% 0.20/0.43  % (3270)Time elapsed: 0.013 s
% 0.20/0.43  % (3270)------------------------------
% 0.20/0.43  % (3270)------------------------------
% 0.20/0.43  % (3265)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (3258)Success in time 0.074 s
%------------------------------------------------------------------------------
