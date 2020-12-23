%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 182 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   21
%              Number of atoms          :  224 ( 467 expanded)
%              Number of equality atoms :   78 ( 177 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(resolution,[],[f137,f90])).

fof(f90,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f89])).

% (13197)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f89,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f74])).

% (13172)Refutation not found, incomplete strategy% (13172)------------------------------
% (13172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13172)Termination reason: Refutation not found, incomplete strategy

% (13172)Memory used [KB]: 6268
% (13172)Time elapsed: 0.128 s
% (13172)------------------------------
% (13172)------------------------------
fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f137,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f136,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f136,plain,(
    v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f135,f40])).

fof(f40,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f135,plain,
    ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = k1_funct_1(sK3,sK2) ),
    inference(resolution,[],[f134,f39])).

fof(f39,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,sK0)
      | sK1 = k1_funct_1(sK3,X0)
      | sK1 = k1_funct_1(sK3,X0)
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f132,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f64,f48])).

% (13189)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f131,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f131,plain,(
    ! [X0] :
      ( m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f130,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | m1_subset_1(X0,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f102,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f102,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f101,f99])).

fof(f99,plain,(
    k2_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f50,f70])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f38,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f101,plain,(
    m1_subset_1(k2_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3),k1_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(resolution,[],[f52,f70])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f130,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f129,f97])).

fof(f97,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f49,f70])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f129,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f128,f36])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) ) ),
    inference(superposition,[],[f46,f126])).

fof(f126,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f122,f95])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

% (13196)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (13176)Refutation not found, incomplete strategy% (13176)------------------------------
% (13176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13176)Termination reason: Refutation not found, incomplete strategy

% (13176)Memory used [KB]: 10746
% (13176)Time elapsed: 0.113 s
% (13176)------------------------------
% (13176)------------------------------
fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f122,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | sK0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f90,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f110,f100])).

fof(f100,plain,(
    k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f51,f70])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f110,plain,
    ( sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f109,f71])).

fof(f71,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f37,f69])).

fof(f37,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f58,f70])).

% (13183)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:31:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (13172)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (13171)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (13174)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13190)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (13176)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13187)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (13174)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (13180)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (13195)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (13182)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f137,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X4,X2,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X1,X2))) )),
% 0.22/0.54    inference(equality_resolution,[],[f89])).
% 0.22/0.54  % (13197)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X4,X4,X1,X2) != X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f74])).
% 0.22/0.54  % (13172)Refutation not found, incomplete strategy% (13172)------------------------------
% 0.22/0.54  % (13172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13172)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13172)Memory used [KB]: 6268
% 0.22/0.54  % (13172)Time elapsed: 0.128 s
% 0.22/0.54  % (13172)------------------------------
% 0.22/0.54  % (13172)------------------------------
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f65,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 0.22/0.54    inference(resolution,[],[f136,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f135,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    sK1 != k1_funct_1(sK3,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = k1_funct_1(sK3,sK2)),
% 0.22/0.54    inference(resolution,[],[f134,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    r2_hidden(sK2,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = k1_funct_1(sK3,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X0] : (v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0) | sK1 = k1_funct_1(sK3,X0)) )),
% 0.22/0.54    inference(resolution,[],[f132,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.22/0.54    inference(equality_resolution,[],[f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f64,f48])).
% 0.22/0.54  % (13189)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f131,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f130,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | m1_subset_1(X0,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 0.22/0.54    inference(resolution,[],[f102,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f101,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    k2_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k2_relat_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f50,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f42,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f44,f48])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    m1_subset_1(k2_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3),k1_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.22/0.54    inference(resolution,[],[f52,f70])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f129,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    v1_relat_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f49,f70])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f128,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) )),
% 0.22/0.54    inference(superposition,[],[f46,f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f122,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(resolution,[],[f47,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  % (13196)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (13176)Refutation not found, incomplete strategy% (13176)------------------------------
% 0.22/0.54  % (13176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13176)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13176)Memory used [KB]: 10746
% 0.22/0.54  % (13176)Time elapsed: 0.113 s
% 0.22/0.54  % (13176)------------------------------
% 0.22/0.54  % (13176)------------------------------
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_xboole_0) | sK0 = k1_relat_1(sK3)),
% 0.22/0.54    inference(superposition,[],[f90,f111])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relat_1(sK3)),
% 0.22/0.54    inference(superposition,[],[f110,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) = k1_relat_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f51,f70])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f109,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f69])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.54    inference(resolution,[],[f58,f70])).
% 0.22/0.54  % (13183)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (13174)------------------------------
% 0.22/0.54  % (13174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13174)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (13174)Memory used [KB]: 6268
% 0.22/0.54  % (13174)Time elapsed: 0.128 s
% 0.22/0.54  % (13174)------------------------------
% 0.22/0.54  % (13174)------------------------------
% 1.27/0.54  % (13167)Success in time 0.177 s
%------------------------------------------------------------------------------
