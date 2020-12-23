%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 (1334 expanded)
%              Number of leaves         :   15 ( 324 expanded)
%              Depth                    :   28
%              Number of atoms          :  437 (7237 expanded)
%              Number of equality atoms :   72 ( 214 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(resolution,[],[f294,f85])).

fof(f85,plain,(
    ! [X2] : r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2)) ),
    inference(resolution,[],[f78,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f294,plain,(
    ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f228,f292])).

fof(f292,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(resolution,[],[f287,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) ) ),
    inference(forward_demodulation,[],[f284,f189])).

fof(f189,plain,(
    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f115,f187])).

fof(f187,plain,(
    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(resolution,[],[f185,f164])).

fof(f164,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f158,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f158,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f154,f49])).

fof(f154,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f153,f46])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f153,plain,
    ( ~ v1_funct_1(sK1)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f152,f48])).

fof(f48,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f152,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(forward_demodulation,[],[f150,f123])).

fof(f123,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f122,f49])).

fof(f122,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f120,f46])).

fof(f120,plain,
    ( ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f116,f48])).

fof(f116,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f66,f47])).

% (9383)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f185,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(resolution,[],[f182,f128])).

fof(f128,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f119,f123])).

fof(f119,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f118,f49])).

fof(f118,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f117,f46])).

fof(f117,plain,
    ( ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f112,f48])).

% (9376)Refutation not found, incomplete strategy% (9376)------------------------------
% (9376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f112,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f182,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f175,f180])).

fof(f180,plain,(
    sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f165,f128])).

fof(f165,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f159,f162])).

fof(f162,plain,(
    k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f158,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f158,f143])).

fof(f143,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f136,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f136,plain,(
    v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(resolution,[],[f135,f49])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(resolution,[],[f134,f46])).

fof(f134,plain,
    ( ~ v1_funct_1(sK1)
    | v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f129,f48])).

fof(f129,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(backward_demodulation,[],[f121,f123])).

fof(f121,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f64,f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f175,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f174,f115])).

fof(f174,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f170,f99])).

fof(f99,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f97,f79])).

fof(f79,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f68,f49])).

fof(f97,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f96,f46])).

fof(f96,plain,
    ( ~ v1_funct_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f93,plain,(
    v2_funct_1(sK1) ),
    inference(resolution,[],[f92,f49])).

fof(f92,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f91,f46])).

fof(f91,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f170,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f167,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f167,plain,(
    v2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f161,f128])).

fof(f161,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f158,f149])).

fof(f149,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f147,f71])).

fof(f147,plain,(
    v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(resolution,[],[f146,f49])).

fof(f146,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    inference(resolution,[],[f145,f46])).

fof(f145,plain,
    ( ~ v1_funct_1(sK1)
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f138,f48])).

fof(f138,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(forward_demodulation,[],[f137,f123])).

fof(f137,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f65,f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(resolution,[],[f114,f79])).

fof(f114,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(resolution,[],[f94,f46])).

fof(f94,plain,
    ( ~ v1_funct_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f284,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f283,f46])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f282,f79])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f220,f46])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f156,f158])).

fof(f156,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ m1_subset_1(k2_funct_1(X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_partfun1(X9,X10,X6,X7,k2_funct_1(X8),X5) = k5_relat_1(k2_funct_1(X8),X5)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f74,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f228,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f130,f227])).

fof(f227,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f225,f158])).

fof(f225,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1)) ) ),
    inference(forward_demodulation,[],[f224,f113])).

fof(f113,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f111,f79])).

fof(f111,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    inference(resolution,[],[f109,f46])).

fof(f109,plain,
    ( ~ v1_funct_1(sK1)
    | k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f95,f108])).

fof(f108,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f107,f49])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f106,f46])).

fof(f106,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f105,f86])).

fof(f86,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f69,f49])).

fof(f105,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f67,f47])).

fof(f95,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f93,f58])).

fof(f224,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1)) ) ),
    inference(resolution,[],[f184,f128])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0) ) ),
    inference(resolution,[],[f155,f49])).

fof(f155,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f74,f46])).

fof(f130,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f124,f123])).

fof(f124,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f75,f123])).

fof(f75,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f50,f51,f51])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:10:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (9374)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.46  % (9366)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (9378)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % (9368)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (9366)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (9381)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (9376)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (9370)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (9369)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (9371)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (9377)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (9372)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f295,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(resolution,[],[f294,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X2] : (r2_relset_1(X2,X2,k6_relat_1(X2),k6_relat_1(X2))) )),
% 0.22/0.48    inference(resolution,[],[f78,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f53,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.48    inference(condensation,[],[f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.48  fof(f294,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f293])).
% 0.22/0.48  fof(f293,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f228,f292])).
% 0.22/0.48  fof(f292,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.22/0.48    inference(resolution,[],[f287,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.48    inference(negated_conjecture,[],[f16])).
% 0.22/0.48  fof(f16,conjecture,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.22/0.48  fof(f287,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f284,f189])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f115,f187])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f185,f164])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f158,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(resolution,[],[f154,f49])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(resolution,[],[f153,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f43])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(resolution,[],[f152,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f43])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(forward_demodulation,[],[f150,f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f122,f49])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f120,f46])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(resolution,[],[f116,f48])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f62,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f43])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f66,f47])).
% 0.22/0.48  % (9383)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    ~v1_relat_1(k2_funct_1(sK1)) | k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f182,f128])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f119,f123])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f118,f49])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f117,f46])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(resolution,[],[f112,f48])).
% 0.22/0.48  % (9376)Refutation not found, incomplete strategy% (9376)------------------------------
% 0.22/0.48  % (9376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f63,f47])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1)) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    ~v1_funct_1(k2_funct_1(sK1)) | k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f175,f180])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    sK0 = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f165,f128])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    ~v1_funct_1(k2_funct_1(sK1)) | sK0 = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f159,f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f158,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f158,f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f136,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.48    inference(resolution,[],[f135,f49])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.48    inference(resolution,[],[f134,f46])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(resolution,[],[f129,f48])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f121,f123])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.48    inference(resolution,[],[f64,f47])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    k6_relat_1(k2_relat_1(sK1)) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f174,f115])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f170,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f97,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f68,f49])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f96,f46])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f93,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    v2_funct_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f92,f49])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v2_funct_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f91,f46])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    inference(resolution,[],[f71,f48])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f167,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f161,f128])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f158,f149])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f147,f71])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.49    inference(resolution,[],[f146,f49])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.49    inference(resolution,[],[f145,f46])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    inference(resolution,[],[f138,f48])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f137,f123])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f65,f47])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f114,f79])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f94,f46])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f93,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(resolution,[],[f283,f46])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.49    inference(resolution,[],[f282,f79])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(sK1) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.49    inference(resolution,[],[f220,f46])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.49    inference(resolution,[],[f156,f158])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X6,X10,X8,X7,X5,X9] : (~m1_subset_1(k2_funct_1(X8),k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_partfun1(X9,X10,X6,X7,k2_funct_1(X8),X5) = k5_relat_1(k2_funct_1(X8),X5) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 0.22/0.49    inference(resolution,[],[f74,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.49    inference(flattening,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.22/0.49    inference(backward_demodulation,[],[f130,f227])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f225,f158])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k6_relat_1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f224,f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f111,f79])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f109,f46])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(backward_demodulation,[],[f95,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f107,f49])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f106,f46])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relat_1(sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f105,f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f69,f49])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f67,f47])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f93,f58])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1))) )),
% 0.22/0.49    inference(resolution,[],[f184,f128])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f155,f49])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f74,f46])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f124,f123])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.22/0.49    inference(backward_demodulation,[],[f75,f123])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.22/0.49    inference(definition_unfolding,[],[f50,f51,f51])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f43])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (9366)------------------------------
% 0.22/0.49  % (9366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9366)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (9366)Memory used [KB]: 1791
% 0.22/0.49  % (9366)Time elapsed: 0.053 s
% 0.22/0.49  % (9366)------------------------------
% 0.22/0.49  % (9366)------------------------------
% 0.22/0.49  % (9376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9376)Memory used [KB]: 10874
% 0.22/0.49  % (9376)Time elapsed: 0.062 s
% 0.22/0.49  % (9376)------------------------------
% 0.22/0.49  % (9376)------------------------------
% 0.22/0.49  % (9359)Success in time 0.129 s
%------------------------------------------------------------------------------
