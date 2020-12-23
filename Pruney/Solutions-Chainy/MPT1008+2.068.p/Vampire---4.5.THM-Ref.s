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
% DateTime   : Thu Dec  3 13:04:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 513 expanded)
%              Number of leaves         :   17 ( 146 expanded)
%              Depth                    :   22
%              Number of atoms          :  264 (1086 expanded)
%              Number of equality atoms :  141 ( 620 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(subsumption_resolution,[],[f223,f108])).

fof(f108,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f72,f97])).

fof(f97,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f38,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f72,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f40,f71,f71])).

fof(f40,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f223,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f219])).

fof(f219,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f150,f195])).

fof(f195,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f194,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f105,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X0,X0,X1,X2) = X3
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f61,f71,f71,f71,f70,f70,f70,f55,f55])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X3
      | k1_tarski(X0) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X2) = X3
      | k2_tarski(X0,X1) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k1_enumset1(X0,X1,X2) = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f105,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f100,f104])).

fof(f104,plain,(
    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f99,f95])).

fof(f95,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f98,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

% (24709)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f100,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),X1) ),
    inference(resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f194,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f188,f108])).

fof(f188,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f150,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f161,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f160,f42])).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f160,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f157,f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[],[f101,f107])).

fof(f101,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f98,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f157,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f155,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f155,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relat_1(sK2))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f154,f97])).

fof(f154,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f153,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f153,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f151,f74])).

fof(f74,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f37,f71])).

% (24691)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f37,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f151,plain,
    ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f149,f73])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(sK2,sK3(X0)),k2_relset_1(X0,X1,sK2))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f36,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

% (24711)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f150,plain,(
    ! [X3] :
      ( k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) ) ),
    inference(subsumption_resolution,[],[f94,f98])).

fof(f94,plain,(
    ! [X3] :
      ( ~ v1_relat_1(sK2)
      | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) ) ),
    inference(resolution,[],[f36,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f52,f71,f71])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (24695)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (24720)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.50  % (24692)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (24712)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (24694)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (24693)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (24700)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (24690)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (24712)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (24696)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (24698)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (24702)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.52  % (24713)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (24710)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.52  % (24702)Refutation not found, incomplete strategy% (24702)------------------------------
% 1.25/0.52  % (24702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (24702)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (24702)Memory used [KB]: 10618
% 1.25/0.52  % (24702)Time elapsed: 0.107 s
% 1.25/0.52  % (24702)------------------------------
% 1.25/0.52  % (24702)------------------------------
% 1.25/0.52  % (24699)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.52  % (24718)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.52  % (24706)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f227,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(subsumption_resolution,[],[f223,f108])).
% 1.25/0.52  fof(f108,plain,(
% 1.25/0.52    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.25/0.52    inference(backward_demodulation,[],[f72,f97])).
% 1.25/0.52  fof(f97,plain,(
% 1.25/0.52    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.25/0.52    inference(resolution,[],[f73,f57])).
% 1.25/0.52  fof(f57,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f31])).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.25/0.52  fof(f73,plain,(
% 1.25/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.25/0.52    inference(definition_unfolding,[],[f38,f71])).
% 1.25/0.52  fof(f71,plain,(
% 1.25/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.52    inference(definition_unfolding,[],[f44,f70])).
% 1.25/0.52  fof(f70,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.52    inference(definition_unfolding,[],[f50,f55])).
% 1.25/0.52  fof(f55,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f3])).
% 1.25/0.52  fof(f3,axiom,(
% 1.25/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.52  fof(f44,plain,(
% 1.25/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.52  fof(f38,plain,(
% 1.25/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.25/0.52    inference(flattening,[],[f19])).
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.25/0.52    inference(ennf_transformation,[],[f18])).
% 1.25/0.52  fof(f18,negated_conjecture,(
% 1.25/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.25/0.52    inference(negated_conjecture,[],[f17])).
% 1.25/0.52  fof(f17,conjecture,(
% 1.25/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 1.25/0.52  fof(f72,plain,(
% 1.25/0.52    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.25/0.52    inference(definition_unfolding,[],[f40,f71,f71])).
% 1.25/0.52  fof(f40,plain,(
% 1.25/0.52    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f223,plain,(
% 1.25/0.52    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 1.25/0.52    inference(trivial_inequality_removal,[],[f219])).
% 1.25/0.52  fof(f219,plain,(
% 1.25/0.52    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 1.25/0.52    inference(superposition,[],[f150,f195])).
% 1.25/0.52  fof(f195,plain,(
% 1.25/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(subsumption_resolution,[],[f194,f107])).
% 1.25/0.52  fof(f107,plain,(
% 1.25/0.52    k1_xboole_0 = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f106])).
% 1.25/0.52  fof(f106,plain,(
% 1.25/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.25/0.52    inference(resolution,[],[f105,f84])).
% 1.25/0.52  fof(f84,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X0) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X0,X0,X1,X2) = X3 | k1_xboole_0 = X3) )),
% 1.25/0.52    inference(definition_unfolding,[],[f61,f71,f71,f71,f70,f70,f70,f55,f55])).
% 1.25/0.52  fof(f61,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X3 | k1_tarski(X0) = X3 | k1_tarski(X1) = X3 | k1_tarski(X2) = X3 | k2_tarski(X0,X1) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k1_enumset1(X0,X1,X2) = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f35])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.25/0.52    inference(ennf_transformation,[],[f5])).
% 1.25/0.52  fof(f5,axiom,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.25/0.52  fof(f105,plain,(
% 1.25/0.52    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.25/0.52    inference(superposition,[],[f100,f104])).
% 1.25/0.52  fof(f104,plain,(
% 1.25/0.52    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.25/0.52    inference(resolution,[],[f99,f95])).
% 1.25/0.52  fof(f95,plain,(
% 1.25/0.52    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.25/0.52    inference(resolution,[],[f73,f58])).
% 1.25/0.52  fof(f58,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f13])).
% 1.25/0.52  fof(f13,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.25/0.52  fof(f99,plain,(
% 1.25/0.52    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.25/0.52    inference(resolution,[],[f98,f53])).
% 1.25/0.52  fof(f53,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f28])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.25/0.52  fof(f98,plain,(
% 1.25/0.52    v1_relat_1(sK2)),
% 1.25/0.52    inference(resolution,[],[f73,f56])).
% 1.25/0.52  fof(f56,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f30])).
% 1.25/0.52  fof(f30,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f12])).
% 1.25/0.52  fof(f12,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.25/0.52  % (24709)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  fof(f100,plain,(
% 1.25/0.52    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),X1)) )),
% 1.25/0.52    inference(resolution,[],[f98,f51])).
% 1.25/0.52  fof(f51,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f9])).
% 1.25/0.52  fof(f9,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.25/0.52  fof(f194,plain,(
% 1.25/0.52    k1_xboole_0 != k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(subsumption_resolution,[],[f188,f108])).
% 1.25/0.52  fof(f188,plain,(
% 1.25/0.52    k1_xboole_0 != k1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(superposition,[],[f150,f162])).
% 1.25/0.52  fof(f162,plain,(
% 1.25/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(subsumption_resolution,[],[f161,f43])).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.25/0.52  fof(f161,plain,(
% 1.25/0.52    ~r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(forward_demodulation,[],[f160,f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.25/0.52    inference(cnf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.25/0.52  fof(f160,plain,(
% 1.25/0.52    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(superposition,[],[f157,f111])).
% 1.25/0.52  fof(f111,plain,(
% 1.25/0.52    k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(trivial_inequality_removal,[],[f110])).
% 1.25/0.52  fof(f110,plain,(
% 1.25/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.25/0.52    inference(superposition,[],[f101,f107])).
% 1.25/0.52  fof(f101,plain,(
% 1.25/0.52    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.25/0.52    inference(resolution,[],[f98,f45])).
% 1.25/0.52  fof(f45,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f8])).
% 1.25/0.52  fof(f8,axiom,(
% 1.25/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.25/0.52  fof(f157,plain,(
% 1.25/0.52    ~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.25/0.52    inference(resolution,[],[f155,f54])).
% 1.25/0.52  fof(f54,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f11])).
% 1.25/0.52  fof(f11,axiom,(
% 1.25/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.25/0.52  fof(f155,plain,(
% 1.25/0.52    r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relat_1(sK2)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.25/0.52    inference(forward_demodulation,[],[f154,f97])).
% 1.25/0.52  fof(f154,plain,(
% 1.25/0.52    r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f153,f39])).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    k1_xboole_0 != sK1),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f153,plain,(
% 1.25/0.52    k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f151,f74])).
% 1.25/0.52  fof(f74,plain,(
% 1.25/0.52    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.52    inference(definition_unfolding,[],[f37,f71])).
% 1.25/0.52  % (24691)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f151,plain,(
% 1.25/0.52    ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.25/0.52    inference(resolution,[],[f149,f73])).
% 1.25/0.52  fof(f149,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(sK2,sK3(X0)),k2_relset_1(X0,X1,sK2)) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(resolution,[],[f93,f49])).
% 1.25/0.52  fof(f49,plain,(
% 1.25/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.25/0.52    inference(ennf_transformation,[],[f15])).
% 1.25/0.52  fof(f15,axiom,(
% 1.25/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.25/0.52  fof(f93,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2))) )),
% 1.25/0.52    inference(resolution,[],[f36,f60])).
% 1.25/0.52  fof(f60,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f34])).
% 1.25/0.52  % (24711)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.25/0.52    inference(flattening,[],[f33])).
% 1.25/0.52  fof(f33,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.25/0.52    inference(ennf_transformation,[],[f16])).
% 1.25/0.53  fof(f16,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    v1_funct_1(sK2)),
% 1.25/0.53    inference(cnf_transformation,[],[f20])).
% 1.25/0.53  fof(f150,plain,(
% 1.25/0.53    ( ! [X3] : (k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) )),
% 1.25/0.53    inference(subsumption_resolution,[],[f94,f98])).
% 1.25/0.53  fof(f94,plain,(
% 1.25/0.53    ( ! [X3] : (~v1_relat_1(sK2) | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) )),
% 1.25/0.53    inference(resolution,[],[f36,f75])).
% 1.25/0.53  fof(f75,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f52,f71,f71])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(flattening,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (24712)------------------------------
% 1.25/0.53  % (24712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (24712)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (24712)Memory used [KB]: 1791
% 1.25/0.53  % (24712)Time elapsed: 0.109 s
% 1.25/0.53  % (24712)------------------------------
% 1.25/0.53  % (24712)------------------------------
% 1.25/0.53  % (24717)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.53  % (24687)Success in time 0.17 s
%------------------------------------------------------------------------------
