%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0823+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 136 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 339 expanded)
%              Number of equality atoms :   48 ( 190 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3658,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3657,f2484])).

fof(f2484,plain,(
    k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f2483,f2286])).

fof(f2286,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f2242,f2244])).

fof(f2244,plain,(
    k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f1636,f1645])).

fof(f1645,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1246])).

fof(f1246,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1220])).

fof(f1220,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f1636,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1449])).

fof(f1449,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
      | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1240,f1448])).

fof(f1448,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
        | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f1240,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1231])).

fof(f1231,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f1230])).

fof(f1230,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f2242,plain,(
    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f1636,f1643])).

fof(f1643,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1244])).

fof(f1244,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f2483,plain,
    ( k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2482,f2349])).

fof(f2349,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f2263,f1837])).

fof(f1837,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1345])).

fof(f1345,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f838])).

fof(f838,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f2263,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f1720,f1636,f1677])).

fof(f1677,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1267])).

fof(f1267,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1720,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f2482,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f2287,f1650])).

fof(f1650,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1249])).

fof(f1249,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1219])).

fof(f1219,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2287,plain,
    ( k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f2284,f2241])).

fof(f2241,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f1636,f1642])).

fof(f1642,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1243,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1218])).

fof(f1218,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2284,plain,
    ( k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f2283,f2244])).

fof(f2283,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f2281,f2244])).

fof(f2281,plain,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relat_1(sK2)
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f1637,f2246])).

fof(f2246,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f1636,f1650])).

fof(f1637,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1449])).

fof(f3657,plain,(
    k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f3613,f2348])).

fof(f2348,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f2263,f1836])).

fof(f1836,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1345])).

fof(f3613,plain,(
    k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f2286,f1642])).
%------------------------------------------------------------------------------
