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
% DateTime   : Thu Dec  3 13:02:25 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 330 expanded)
%              Number of leaves         :   11 (  81 expanded)
%              Depth                    :   38
%              Number of atoms          :  303 (1882 expanded)
%              Number of equality atoms :   24 ( 221 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f141,plain,(
    ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f139,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f138,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f138,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f31])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f54])).

fof(f54,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f30])).

fof(f53,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f52,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f52,plain,(
    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f135,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f131,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f131,plain,(
    ~ m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f130,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f130,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f129,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f122,f30])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f121,f34])).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(subsumption_resolution,[],[f120,f28])).

fof(f120,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f115,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f115,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(subsumption_resolution,[],[f69,f114])).

fof(f114,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f113,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f95,f30])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f94,f34])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f93,f51])).

fof(f51,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f50,f32])).

fof(f32,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f93,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f92,f28])).

fof(f92,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f91,f31])).

fof(f91,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f88,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) ),
    inference(resolution,[],[f87,f54])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) ) ),
    inference(resolution,[],[f86,f43])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) ) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f83,f30])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f79,f34])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f78,f28])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f75,f38])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) ) ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f73,f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f70,f34])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) ) ),
    inference(resolution,[],[f58,f28])).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f69,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f68,f33])).

fof(f33,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f67,f39])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f65,f34])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(forward_demodulation,[],[f64,f51])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f63,f28])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:21:16 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.42  % (30934)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.43  % (30919)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.43  % (30925)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.44  % (30925)Refutation not found, incomplete strategy% (30925)------------------------------
% 0.19/0.44  % (30925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (30934)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % (30927)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.45  % (30925)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (30925)Memory used [KB]: 10618
% 0.19/0.45  % (30925)Time elapsed: 0.073 s
% 0.19/0.45  % (30925)------------------------------
% 0.19/0.45  % (30925)------------------------------
% 0.19/0.45  % (30921)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.45  % (30917)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.45  % (30915)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f142,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(subsumption_resolution,[],[f141,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.45  fof(f141,plain,(
% 0.19/0.45    ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.45    inference(resolution,[],[f139,f30])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.45    inference(cnf_transformation,[],[f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.45    inference(ennf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.45    inference(negated_conjecture,[],[f10])).
% 0.19/0.45  fof(f10,conjecture,(
% 0.19/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.19/0.45  fof(f139,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(resolution,[],[f138,f34])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.45  fof(f138,plain,(
% 0.19/0.45    ~v1_relat_1(sK2)),
% 0.19/0.45    inference(subsumption_resolution,[],[f137,f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    v1_funct_1(sK2)),
% 0.19/0.45    inference(cnf_transformation,[],[f27])).
% 0.19/0.45  fof(f137,plain,(
% 0.19/0.45    ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.45    inference(subsumption_resolution,[],[f136,f31])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    v2_funct_1(sK2)),
% 0.19/0.45    inference(cnf_transformation,[],[f27])).
% 0.19/0.45  fof(f136,plain,(
% 0.19/0.45    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.45    inference(subsumption_resolution,[],[f135,f54])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(subsumption_resolution,[],[f53,f30])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.45    inference(superposition,[],[f52,f45])).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(resolution,[],[f46,f30])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.19/0.45  fof(f135,plain,(
% 0.19/0.45    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.45    inference(superposition,[],[f131,f38])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(flattening,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.19/0.45  fof(f131,plain,(
% 0.19/0.45    ~m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(resolution,[],[f130,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.19/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.46  fof(f130,plain,(
% 0.19/0.46    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f129,f39])).
% 0.19/0.46  fof(f129,plain,(
% 0.19/0.46    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.46    inference(resolution,[],[f122,f30])).
% 0.19/0.46  fof(f122,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(resolution,[],[f121,f34])).
% 0.19/0.46  fof(f121,plain,(
% 0.19/0.46    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f120,f28])).
% 0.19/0.46  fof(f120,plain,(
% 0.19/0.46    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f115,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    ~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f69,f114])).
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.46    inference(subsumption_resolution,[],[f113,f39])).
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.46    inference(resolution,[],[f95,f30])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(resolution,[],[f94,f34])).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    ~v1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.46    inference(forward_demodulation,[],[f93,f51])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    sK1 = k2_relat_1(sK2)),
% 0.19/0.46    inference(forward_demodulation,[],[f50,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f44,f30])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0))) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(subsumption_resolution,[],[f92,f28])).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(subsumption_resolution,[],[f91,f31])).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.46    inference(superposition,[],[f88,f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f19])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))),
% 0.19/0.46    inference(resolution,[],[f87,f54])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))) )),
% 0.19/0.46    inference(resolution,[],[f86,f43])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f85,f39])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) )),
% 0.19/0.46    inference(resolution,[],[f83,f30])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(resolution,[],[f79,f34])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f78,f28])).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f77,f31])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.19/0.46    inference(superposition,[],[f75,f38])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f74,f39])).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) )),
% 0.19/0.46    inference(resolution,[],[f73,f30])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(resolution,[],[f70,f34])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))) )),
% 0.19/0.46    inference(resolution,[],[f58,f28])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~v1_funct_1(X1) | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f56,f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2))) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(resolution,[],[f42,f36])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(flattening,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.19/0.46    inference(resolution,[],[f68,f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f67,f39])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) )),
% 0.19/0.46    inference(resolution,[],[f66,f30])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(resolution,[],[f65,f34])).
% 0.19/0.46  fof(f65,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f64,f51])).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f63,f28])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.19/0.46    inference(resolution,[],[f49,f31])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f48,f35])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f47,f36])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(superposition,[],[f41,f37])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f21])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (30934)------------------------------
% 0.19/0.46  % (30934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (30934)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (30934)Memory used [KB]: 6268
% 0.19/0.46  % (30934)Time elapsed: 0.081 s
% 0.19/0.46  % (30934)------------------------------
% 0.19/0.46  % (30934)------------------------------
% 0.19/0.46  % (30914)Success in time 0.123 s
%------------------------------------------------------------------------------
