%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:23 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 231 expanded)
%              Number of leaves         :   15 (  69 expanded)
%              Depth                    :   26
%              Number of atoms          :  308 (1457 expanded)
%              Number of equality atoms :   51 ( 199 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f38,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f162,f82])).

fof(f82,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_relset_1(X0,X1,X2) != X1
            & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( sK1 != k2_relset_1(sK0,sK1,sK2)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( sK1 != k2_relset_1(sK0,sK1,sK2)
        & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK1 = k2_relat_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) ) ),
    inference(resolution,[],[f152,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_relat_1(X0))
      | k2_relat_1(X0) = X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f74,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f152,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1,k2_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f149,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f51,f57])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f143,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f143,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | r1_tarski(sK1,X5) ) ),
    inference(resolution,[],[f141,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f75,f66])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f139,f36])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f105,f127])).

fof(f127,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f126,f39])).

fof(f126,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f124,f36])).

fof(f124,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f120,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f112,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f112,plain,(
    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f111,f39])).

fof(f111,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f110,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f107,f38])).

fof(f107,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f86,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f83,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f65,f63])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (27071)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (27063)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (27080)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (27090)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (27065)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (27081)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (27066)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (27072)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (27067)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (27071)Refutation not found, incomplete strategy% (27071)------------------------------
% 0.20/0.52  % (27071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27071)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27071)Memory used [KB]: 10746
% 0.20/0.52  % (27071)Time elapsed: 0.108 s
% 0.20/0.52  % (27071)------------------------------
% 0.20/0.52  % (27071)------------------------------
% 0.20/0.52  % (27090)Refutation not found, incomplete strategy% (27090)------------------------------
% 0.20/0.52  % (27090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27090)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27090)Memory used [KB]: 6268
% 0.20/0.52  % (27090)Time elapsed: 0.098 s
% 0.20/0.52  % (27090)------------------------------
% 0.20/0.52  % (27090)------------------------------
% 0.20/0.52  % (27064)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (27070)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (27086)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (27082)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (27073)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (27059)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (27091)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (27091)Refutation not found, incomplete strategy% (27091)------------------------------
% 0.20/0.53  % (27091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27091)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27091)Memory used [KB]: 10874
% 0.20/0.53  % (27091)Time elapsed: 0.123 s
% 0.20/0.53  % (27091)------------------------------
% 0.20/0.53  % (27091)------------------------------
% 0.20/0.53  % (27074)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (27085)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (27061)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (27068)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (27089)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (27069)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (27077)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (27092)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (27084)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (27075)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (27088)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.55  % (27078)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.55  % (27087)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.56  % (27085)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % (27079)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.56  % (27078)Refutation not found, incomplete strategy% (27078)------------------------------
% 1.48/0.56  % (27078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f178,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(unit_resulting_resolution,[],[f38,f38,f164])).
% 1.48/0.57  fof(f164,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f162,f82])).
% 1.48/0.57  fof(f82,plain,(
% 1.48/0.57    sK1 != k2_relat_1(sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f81,f38])).
% 1.48/0.57  fof(f81,plain,(
% 1.48/0.57    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.57    inference(superposition,[],[f43,f58])).
% 1.48/0.57  fof(f58,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f21])).
% 1.48/0.57  fof(f21,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.57    inference(ennf_transformation,[],[f6])).
% 1.48/0.57  fof(f6,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.57  fof(f43,plain,(
% 1.48/0.57    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f31])).
% 1.48/0.57  fof(f31,plain,(
% 1.48/0.57    (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).
% 1.48/0.57  fof(f29,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f30,plain,(
% 1.48/0.57    ? [X3] : (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f16,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.48/0.57    inference(flattening,[],[f15])).
% 1.48/0.57  fof(f15,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,negated_conjecture,(
% 1.48/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.48/0.57    inference(negated_conjecture,[],[f13])).
% 1.48/0.57  fof(f13,conjecture,(
% 1.48/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.48/0.57  fof(f162,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))) )),
% 1.48/0.57    inference(resolution,[],[f152,f77])).
% 1.48/0.57  fof(f77,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_relat_1(X0)) | k2_relat_1(X0) = X2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.48/0.57    inference(resolution,[],[f75,f56])).
% 1.48/0.57  fof(f56,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f34])).
% 1.48/0.57  fof(f34,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(flattening,[],[f33])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(nnf_transformation,[],[f1])).
% 1.48/0.57  fof(f1,axiom,(
% 1.48/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.57  fof(f75,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f74,f57])).
% 1.48/0.57  fof(f57,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f20])).
% 1.48/0.57  fof(f20,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.57    inference(ennf_transformation,[],[f4])).
% 1.48/0.57  fof(f4,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.57  fof(f74,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(resolution,[],[f60,f52])).
% 1.48/0.57  fof(f52,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f32])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(nnf_transformation,[],[f19])).
% 1.48/0.57  fof(f19,plain,(
% 1.48/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f2])).
% 1.48/0.57  fof(f2,axiom,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.48/0.57  fof(f60,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f22])).
% 1.48/0.57  fof(f22,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.57    inference(ennf_transformation,[],[f5])).
% 1.48/0.57  fof(f5,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.48/0.57  fof(f152,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(sK1,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(resolution,[],[f149,f117])).
% 1.48/0.57  fof(f117,plain,(
% 1.48/0.57    ( ! [X0,X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(resolution,[],[f80,f36])).
% 1.48/0.57  fof(f36,plain,(
% 1.48/0.57    v1_funct_1(sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f31])).
% 1.48/0.57  fof(f80,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.48/0.57    inference(resolution,[],[f51,f57])).
% 1.48/0.57  fof(f51,plain,(
% 1.48/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f18])).
% 1.48/0.57  fof(f18,plain,(
% 1.48/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(flattening,[],[f17])).
% 1.48/0.57  fof(f17,plain,(
% 1.48/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.57    inference(ennf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.48/0.57  fof(f149,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,X1)) )),
% 1.48/0.57    inference(resolution,[],[f143,f41])).
% 1.48/0.57  fof(f41,plain,(
% 1.48/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.48/0.57    inference(cnf_transformation,[],[f31])).
% 1.48/0.57  fof(f143,plain,(
% 1.48/0.57    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | r1_tarski(sK1,X5)) )),
% 1.48/0.57    inference(resolution,[],[f141,f78])).
% 1.48/0.57  fof(f78,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(superposition,[],[f75,f66])).
% 1.48/0.57  fof(f66,plain,(
% 1.48/0.57    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.48/0.57    inference(definition_unfolding,[],[f48,f44])).
% 1.48/0.57  fof(f44,plain,(
% 1.48/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f11])).
% 1.48/0.57  fof(f11,axiom,(
% 1.48/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.48/0.57  fof(f48,plain,(
% 1.48/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f3])).
% 1.48/0.57  fof(f3,axiom,(
% 1.48/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.48/0.57  fof(f141,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f140,f39])).
% 1.48/0.57  fof(f39,plain,(
% 1.48/0.57    v1_funct_1(sK3)),
% 1.48/0.57    inference(cnf_transformation,[],[f31])).
% 1.48/0.57  fof(f140,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(sK3)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f139,f36])).
% 1.48/0.57  fof(f139,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(sK3)) )),
% 1.48/0.57    inference(superposition,[],[f105,f127])).
% 1.48/0.57  fof(f127,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f126,f39])).
% 1.48/0.57  fof(f126,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(subsumption_resolution,[],[f125,f41])).
% 1.48/0.57  fof(f125,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(subsumption_resolution,[],[f124,f36])).
% 1.48/0.57  fof(f124,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(subsumption_resolution,[],[f120,f38])).
% 1.48/0.57  fof(f120,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(superposition,[],[f112,f63])).
% 1.48/0.57  fof(f63,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f26])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.57    inference(flattening,[],[f25])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.57    inference(ennf_transformation,[],[f10])).
% 1.48/0.57  fof(f10,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.48/0.57  fof(f112,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f111,f39])).
% 1.48/0.57  fof(f111,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(subsumption_resolution,[],[f110,f41])).
% 1.48/0.57  fof(f110,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(subsumption_resolution,[],[f109,f36])).
% 1.48/0.57  fof(f109,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(subsumption_resolution,[],[f107,f38])).
% 1.48/0.57  fof(f107,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3)),
% 1.48/0.57    inference(resolution,[],[f86,f65])).
% 1.48/0.57  fof(f65,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f28])).
% 1.48/0.57  fof(f28,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.57    inference(flattening,[],[f27])).
% 1.48/0.57  fof(f27,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.57    inference(ennf_transformation,[],[f8])).
% 1.48/0.57  fof(f8,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.48/0.57  fof(f86,plain,(
% 1.48/0.57    ~m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f83,f46])).
% 1.48/0.57  fof(f46,plain,(
% 1.48/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f9])).
% 1.48/0.57  fof(f9,axiom,(
% 1.48/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.48/0.57  fof(f83,plain,(
% 1.48/0.57    k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.48/0.57    inference(resolution,[],[f61,f42])).
% 1.48/0.57  fof(f42,plain,(
% 1.48/0.57    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 1.48/0.57    inference(cnf_transformation,[],[f31])).
% 1.48/0.57  fof(f61,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f35])).
% 1.48/0.57  fof(f35,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.57    inference(nnf_transformation,[],[f24])).
% 1.48/0.57  fof(f24,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.57    inference(flattening,[],[f23])).
% 1.48/0.57  fof(f23,plain,(
% 1.48/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.57    inference(ennf_transformation,[],[f7])).
% 1.48/0.57  fof(f7,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.48/0.57  fof(f105,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f104])).
% 1.48/0.57  fof(f104,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.57    inference(superposition,[],[f65,f63])).
% 1.48/0.57  fof(f38,plain,(
% 1.48/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.57    inference(cnf_transformation,[],[f31])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (27085)------------------------------
% 1.48/0.57  % (27085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (27085)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (27085)Memory used [KB]: 6396
% 1.48/0.57  % (27085)Time elapsed: 0.143 s
% 1.48/0.57  % (27085)------------------------------
% 1.48/0.57  % (27085)------------------------------
% 1.60/0.57  % (27078)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (27078)Memory used [KB]: 10618
% 1.60/0.57  % (27078)Time elapsed: 0.148 s
% 1.60/0.57  % (27078)------------------------------
% 1.60/0.57  % (27078)------------------------------
% 1.60/0.57  % (27055)Success in time 0.21 s
%------------------------------------------------------------------------------
