%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 786 expanded)
%              Number of leaves         :   15 ( 172 expanded)
%              Depth                    :   29
%              Number of atoms          :  274 (2729 expanded)
%              Number of equality atoms :  109 ( 764 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(subsumption_resolution,[],[f416,f303])).

fof(f303,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f258,f282])).

fof(f282,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f280,f84])).

fof(f84,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f33])).

% (3361)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (3357)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (3363)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (3360)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (3374)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (3376)Refutation not found, incomplete strategy% (3376)------------------------------
% (3376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3376)Termination reason: Refutation not found, incomplete strategy

% (3376)Memory used [KB]: 6396
% (3376)Time elapsed: 0.124 s
% (3376)------------------------------
% (3376)------------------------------
% (3377)Termination reason: Refutation not found, incomplete strategy

% (3377)Memory used [KB]: 6268
% (3377)Time elapsed: 0.131 s
% (3377)------------------------------
% (3377)------------------------------
% (3374)Refutation not found, incomplete strategy% (3374)------------------------------
% (3374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3370)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (3366)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (3374)Termination reason: Refutation not found, incomplete strategy

% (3374)Memory used [KB]: 10618
% (3374)Time elapsed: 0.129 s
% (3374)------------------------------
% (3374)------------------------------
% (3360)Refutation not found, incomplete strategy% (3360)------------------------------
% (3360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3360)Termination reason: Refutation not found, incomplete strategy

% (3360)Memory used [KB]: 10746
% (3360)Time elapsed: 0.132 s
% (3360)------------------------------
% (3360)------------------------------
% (3366)Refutation not found, incomplete strategy% (3366)------------------------------
% (3366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3366)Termination reason: Refutation not found, incomplete strategy

% (3366)Memory used [KB]: 10618
% (3366)Time elapsed: 0.137 s
% (3366)------------------------------
% (3366)------------------------------
fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f280,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f49,f258])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f258,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f257,f99])).

fof(f99,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f257,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f217])).

fof(f217,plain,(
    ! [X19] :
      ( k1_tarski(sK0) != k1_tarski(X19)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X19)) ) ),
    inference(subsumption_resolution,[],[f195,f84])).

fof(f195,plain,(
    ! [X19] :
      ( k1_tarski(sK0) != k1_tarski(X19)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X19))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f146,f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k1_tarski(X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v4_relat_1(X2,k1_tarski(X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f62,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f146,plain,(
    k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f144,f84])).

fof(f144,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f141,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f140,f84])).

fof(f140,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f135,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f134,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f134,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f133,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f47,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f416,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f415,f80])).

fof(f80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f53,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f415,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f411,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f411,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f290,f358])).

fof(f358,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k1_relat_1(X1) ) ),
    inference(resolution,[],[f321,f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( r1_tarski(k9_relat_1(X1,X2),k1_xboole_0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X1] :
      ( r1_tarski(k9_relat_1(X1,X2),k1_xboole_0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k1_relat_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f55,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f321,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f320,f80])).

fof(f320,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f319,f282])).

fof(f319,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f318,f164])).

fof(f164,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f128,f78])).

fof(f128,plain,(
    ! [X0,X1] : v4_relat_1(k2_zfmisc_1(X0,X1),X0) ),
    inference(resolution,[],[f100,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f72,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f318,plain,(
    ! [X2] :
      ( ~ v4_relat_1(k1_xboole_0,X2)
      | ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ v1_relat_1(sK3) ) ),
    inference(forward_demodulation,[],[f274,f282])).

fof(f274,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ v4_relat_1(sK3,X2)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f96,f258])).

fof(f96,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(X3))
      | k1_relat_1(X3) = X2
      | ~ v4_relat_1(X3,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f61,f56])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f290,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f134,f282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:58:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (3356)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (3379)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (3350)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (3371)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (3373)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (3379)Refutation not found, incomplete strategy% (3379)------------------------------
% 0.20/0.50  % (3379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3379)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3379)Memory used [KB]: 1663
% 0.20/0.50  % (3379)Time elapsed: 0.101 s
% 0.20/0.50  % (3379)------------------------------
% 0.20/0.50  % (3379)------------------------------
% 0.20/0.50  % (3365)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (3352)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (3355)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (3354)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (3351)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (3359)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (3369)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (3351)Refutation not found, incomplete strategy% (3351)------------------------------
% 0.20/0.51  % (3351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3351)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3351)Memory used [KB]: 1663
% 0.20/0.51  % (3351)Time elapsed: 0.105 s
% 0.20/0.51  % (3351)------------------------------
% 0.20/0.51  % (3351)------------------------------
% 0.20/0.52  % (3362)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (3358)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (3353)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (3372)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (3376)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (3375)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (3378)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (3377)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (3377)Refutation not found, incomplete strategy% (3377)------------------------------
% 0.20/0.53  % (3377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3368)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (3364)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (3368)Refutation not found, incomplete strategy% (3368)------------------------------
% 0.20/0.53  % (3368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3368)Memory used [KB]: 1791
% 0.20/0.53  % (3368)Time elapsed: 0.132 s
% 0.20/0.53  % (3368)------------------------------
% 0.20/0.53  % (3368)------------------------------
% 0.20/0.53  % (3367)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (3364)Refutation not found, incomplete strategy% (3364)------------------------------
% 0.20/0.54  % (3364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3364)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3364)Memory used [KB]: 1791
% 0.20/0.54  % (3364)Time elapsed: 0.128 s
% 0.20/0.54  % (3364)------------------------------
% 0.20/0.54  % (3364)------------------------------
% 0.20/0.54  % (3367)Refutation not found, incomplete strategy% (3367)------------------------------
% 0.20/0.54  % (3367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3367)Memory used [KB]: 1791
% 0.20/0.54  % (3367)Time elapsed: 0.129 s
% 0.20/0.54  % (3367)------------------------------
% 0.20/0.54  % (3367)------------------------------
% 0.20/0.54  % (3359)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f417,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f416,f303])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f258,f282])).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    k1_xboole_0 = sK3),
% 0.20/0.54    inference(subsumption_resolution,[],[f280,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    v1_relat_1(sK3)),
% 0.20/0.54    inference(resolution,[],[f71,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f33])).
% 0.20/0.54  % (3361)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.54  % (3357)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.54  % (3363)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.54  % (3360)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.54  % (3374)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.54  % (3376)Refutation not found, incomplete strategy% (3376)------------------------------
% 1.41/0.54  % (3376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3376)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3376)Memory used [KB]: 6396
% 1.41/0.54  % (3376)Time elapsed: 0.124 s
% 1.41/0.54  % (3376)------------------------------
% 1.41/0.54  % (3376)------------------------------
% 1.41/0.54  % (3377)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3377)Memory used [KB]: 6268
% 1.41/0.54  % (3377)Time elapsed: 0.131 s
% 1.41/0.54  % (3377)------------------------------
% 1.41/0.54  % (3377)------------------------------
% 1.41/0.54  % (3374)Refutation not found, incomplete strategy% (3374)------------------------------
% 1.41/0.54  % (3374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3370)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.55  % (3366)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.55  % (3374)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3374)Memory used [KB]: 10618
% 1.41/0.55  % (3374)Time elapsed: 0.129 s
% 1.41/0.55  % (3374)------------------------------
% 1.41/0.55  % (3374)------------------------------
% 1.41/0.55  % (3360)Refutation not found, incomplete strategy% (3360)------------------------------
% 1.41/0.55  % (3360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3360)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3360)Memory used [KB]: 10746
% 1.41/0.55  % (3360)Time elapsed: 0.132 s
% 1.41/0.55  % (3360)------------------------------
% 1.41/0.55  % (3360)------------------------------
% 1.41/0.55  % (3366)Refutation not found, incomplete strategy% (3366)------------------------------
% 1.41/0.55  % (3366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3366)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3366)Memory used [KB]: 10618
% 1.41/0.55  % (3366)Time elapsed: 0.137 s
% 1.41/0.55  % (3366)------------------------------
% 1.41/0.55  % (3366)------------------------------
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.41/0.55    inference(flattening,[],[f21])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.41/0.55    inference(ennf_transformation,[],[f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.41/0.55    inference(pure_predicate_removal,[],[f18])).
% 1.41/0.55  fof(f18,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.41/0.55    inference(negated_conjecture,[],[f17])).
% 1.41/0.55  fof(f17,conjecture,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.55  fof(f280,plain,(
% 1.41/0.55    k1_xboole_0 = sK3 | ~v1_relat_1(sK3)),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f270])).
% 1.41/0.55  fof(f270,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3)),
% 1.41/0.55    inference(superposition,[],[f49,f258])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.41/0.55  fof(f258,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(sK3)),
% 1.41/0.55    inference(subsumption_resolution,[],[f257,f99])).
% 1.41/0.55  fof(f99,plain,(
% 1.41/0.55    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.41/0.55    inference(resolution,[],[f72,f45])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.41/0.55    inference(pure_predicate_removal,[],[f15])).
% 1.41/0.55  fof(f15,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.41/0.55  fof(f257,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(sK0))),
% 1.41/0.55    inference(equality_resolution,[],[f217])).
% 1.41/0.55  fof(f217,plain,(
% 1.41/0.55    ( ! [X19] : (k1_tarski(sK0) != k1_tarski(X19) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X19))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f195,f84])).
% 1.41/0.55  fof(f195,plain,(
% 1.41/0.55    ( ! [X19] : (k1_tarski(sK0) != k1_tarski(X19) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X19)) | ~v1_relat_1(sK3)) )),
% 1.41/0.55    inference(superposition,[],[f146,f125])).
% 1.41/0.55  fof(f125,plain,(
% 1.41/0.55    ( ! [X2,X3] : (k1_relat_1(X2) = k1_tarski(X3) | k1_xboole_0 = k1_relat_1(X2) | ~v4_relat_1(X2,k1_tarski(X3)) | ~v1_relat_1(X2)) )),
% 1.41/0.55    inference(resolution,[],[f62,f56])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.41/0.55  fof(f62,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f40])).
% 1.41/0.55  fof(f40,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.41/0.55    inference(flattening,[],[f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.41/0.55    inference(nnf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.41/0.55  fof(f146,plain,(
% 1.41/0.55    k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.41/0.55    inference(subsumption_resolution,[],[f144,f84])).
% 1.41/0.55  fof(f144,plain,(
% 1.41/0.55    k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.41/0.55    inference(resolution,[],[f141,f55])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.41/0.55  fof(f141,plain,(
% 1.41/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.41/0.55    inference(subsumption_resolution,[],[f140,f84])).
% 1.41/0.55  fof(f140,plain,(
% 1.41/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.41/0.55    inference(subsumption_resolution,[],[f135,f44])).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    v1_funct_1(sK3)),
% 1.41/0.55    inference(cnf_transformation,[],[f34])).
% 1.41/0.55  fof(f135,plain,(
% 1.41/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.41/0.55    inference(superposition,[],[f134,f58])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(flattening,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.41/0.55  fof(f134,plain,(
% 1.41/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.41/0.55    inference(subsumption_resolution,[],[f133,f45])).
% 1.41/0.55  fof(f133,plain,(
% 1.41/0.55    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.41/0.55    inference(superposition,[],[f47,f73])).
% 1.41/0.55  fof(f73,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f32])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f16])).
% 1.41/0.55  fof(f16,axiom,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.41/0.55    inference(cnf_transformation,[],[f34])).
% 1.41/0.55  fof(f416,plain,(
% 1.41/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(subsumption_resolution,[],[f415,f80])).
% 1.41/0.55  fof(f80,plain,(
% 1.41/0.55    v1_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(superposition,[],[f53,f78])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f69])).
% 1.41/0.55  fof(f69,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f43])).
% 1.41/0.55  fof(f43,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.55    inference(flattening,[],[f42])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.55    inference(nnf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.41/0.55  fof(f415,plain,(
% 1.41/0.55    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(subsumption_resolution,[],[f411,f77])).
% 1.41/0.55  fof(f77,plain,(
% 1.41/0.55    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.41/0.55    inference(equality_resolution,[],[f63])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f40])).
% 1.41/0.55  fof(f411,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(superposition,[],[f290,f358])).
% 1.41/0.55  fof(f358,plain,(
% 1.41/0.55    ( ! [X2,X1] : (k1_xboole_0 = k9_relat_1(X1,X2) | ~v1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X1)) )),
% 1.41/0.55    inference(resolution,[],[f321,f105])).
% 1.41/0.55  fof(f105,plain,(
% 1.41/0.55    ( ! [X2,X1] : (r1_tarski(k9_relat_1(X1,X2),k1_xboole_0) | ~v1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X1)) )),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f104])).
% 1.41/0.55  fof(f104,plain,(
% 1.41/0.55    ( ! [X2,X1] : (r1_tarski(k9_relat_1(X1,X2),k1_xboole_0) | ~v1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(superposition,[],[f55,f51])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f35])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(nnf_transformation,[],[f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.41/0.55  fof(f321,plain,(
% 1.41/0.55    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f320,f80])).
% 1.41/0.55  fof(f320,plain,(
% 1.41/0.55    ( ! [X2] : (~v1_relat_1(k1_xboole_0) | ~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 1.41/0.55    inference(forward_demodulation,[],[f319,f282])).
% 1.41/0.55  fof(f319,plain,(
% 1.41/0.55    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2 | ~v1_relat_1(sK3)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f318,f164])).
% 1.41/0.55  fof(f164,plain,(
% 1.41/0.55    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.41/0.55    inference(superposition,[],[f128,f78])).
% 1.41/0.55  fof(f128,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v4_relat_1(k2_zfmisc_1(X0,X1),X0)) )),
% 1.41/0.55    inference(resolution,[],[f100,f74])).
% 1.41/0.55  fof(f74,plain,(
% 1.41/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.55    inference(equality_resolution,[],[f60])).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f38])).
% 1.41/0.55  fof(f38,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(flattening,[],[f37])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.55  fof(f100,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 1.41/0.55    inference(resolution,[],[f72,f66])).
% 1.41/0.55  fof(f66,plain,(
% 1.41/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.41/0.55    inference(nnf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.55  fof(f318,plain,(
% 1.41/0.55    ( ! [X2] : (~v4_relat_1(k1_xboole_0,X2) | ~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2 | ~v1_relat_1(sK3)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f274,f282])).
% 1.41/0.55  fof(f274,plain,(
% 1.41/0.55    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2 | ~v4_relat_1(sK3,X2) | ~v1_relat_1(sK3)) )),
% 1.41/0.55    inference(superposition,[],[f96,f258])).
% 1.41/0.55  fof(f96,plain,(
% 1.41/0.55    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(X3)) | k1_relat_1(X3) = X2 | ~v4_relat_1(X3,X2) | ~v1_relat_1(X3)) )),
% 1.41/0.55    inference(resolution,[],[f61,f56])).
% 1.41/0.55  fof(f61,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f38])).
% 1.41/0.55  fof(f290,plain,(
% 1.41/0.55    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.41/0.55    inference(backward_demodulation,[],[f134,f282])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (3359)------------------------------
% 1.41/0.55  % (3359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3359)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (3359)Memory used [KB]: 1918
% 1.41/0.55  % (3359)Time elapsed: 0.112 s
% 1.41/0.55  % (3359)------------------------------
% 1.41/0.55  % (3359)------------------------------
% 1.41/0.55  % (3349)Success in time 0.198 s
%------------------------------------------------------------------------------
