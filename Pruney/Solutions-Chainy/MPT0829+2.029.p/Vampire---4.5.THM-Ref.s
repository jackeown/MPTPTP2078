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
% DateTime   : Thu Dec  3 12:56:44 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 136 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   20
%              Number of atoms          :  162 ( 422 expanded)
%              Number of equality atoms :   38 ( 105 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f72])).

fof(f72,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

% (15809)Refutation not found, incomplete strategy% (15809)------------------------------
% (15809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15809)Termination reason: Refutation not found, incomplete strategy

% (15809)Memory used [KB]: 10618
% (15809)Time elapsed: 0.132 s
% (15809)------------------------------
% (15809)------------------------------
fof(f28,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f71,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f70,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f70,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f32,f69])).

fof(f69,plain,(
    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f68,f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,k1_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f32,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f107,f34])).

% (15822)Refutation not found, incomplete strategy% (15822)------------------------------
% (15822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

% (15822)Termination reason: Refutation not found, incomplete strategy

% (15822)Memory used [KB]: 1663
% (15822)Time elapsed: 0.133 s
% (15822)------------------------------
% (15822)------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f107,plain,(
    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f34,f102])).

fof(f102,plain,(
    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f101,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f93,f30])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f92,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f51,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f89,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f88,f34])).

fof(f88,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK2))),sK1) ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f86,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK2))),sK1)
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f85,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f85,plain,(
    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f84,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f83,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f81,f42])).

fof(f81,plain,(
    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f80,f30])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,k2_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f45,f31])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15802)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (15811)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (15804)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (15804)Refutation not found, incomplete strategy% (15804)------------------------------
% 0.22/0.54  % (15804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15807)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.54  % (15801)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.54  % (15818)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.55  % (15822)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.55  % (15806)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.55  % (15811)Refutation not found, incomplete strategy% (15811)------------------------------
% 0.22/0.55  % (15811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15811)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15811)Memory used [KB]: 10618
% 0.22/0.55  % (15811)Time elapsed: 0.114 s
% 0.22/0.55  % (15811)------------------------------
% 0.22/0.55  % (15811)------------------------------
% 0.22/0.55  % (15824)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.55  % (15803)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.55  % (15815)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.55  % (15824)Refutation not found, incomplete strategy% (15824)------------------------------
% 0.22/0.55  % (15824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15824)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15824)Memory used [KB]: 10618
% 0.22/0.55  % (15824)Time elapsed: 0.068 s
% 0.22/0.55  % (15824)------------------------------
% 0.22/0.55  % (15824)------------------------------
% 0.22/0.55  % (15804)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15804)Memory used [KB]: 10618
% 0.22/0.55  % (15804)Time elapsed: 0.103 s
% 0.22/0.55  % (15804)------------------------------
% 0.22/0.55  % (15804)------------------------------
% 0.22/0.56  % (15820)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.56  % (15807)Refutation not found, incomplete strategy% (15807)------------------------------
% 0.22/0.56  % (15807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15807)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15807)Memory used [KB]: 10618
% 0.22/0.56  % (15807)Time elapsed: 0.121 s
% 0.22/0.56  % (15807)------------------------------
% 0.22/0.56  % (15807)------------------------------
% 0.22/0.56  % (15812)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.43/0.56  % (15805)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.43/0.56  % (15814)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.43/0.56  % (15808)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.56  % (15816)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.43/0.56  % (15818)Refutation not found, incomplete strategy% (15818)------------------------------
% 1.43/0.56  % (15818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (15818)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (15818)Memory used [KB]: 1663
% 1.43/0.56  % (15818)Time elapsed: 0.118 s
% 1.43/0.56  % (15818)------------------------------
% 1.43/0.56  % (15818)------------------------------
% 1.43/0.56  % (15823)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.43/0.56  % (15820)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % (15809)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.43/0.56  % (15812)Refutation not found, incomplete strategy% (15812)------------------------------
% 1.43/0.56  % (15812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (15812)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (15812)Memory used [KB]: 1663
% 1.43/0.56  % (15812)Time elapsed: 0.124 s
% 1.43/0.56  % (15812)------------------------------
% 1.43/0.56  % (15812)------------------------------
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f114,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(subsumption_resolution,[],[f113,f72])).
% 1.43/0.56  fof(f72,plain,(
% 1.43/0.56    sK1 != k2_relat_1(sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f71,f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  % (15809)Refutation not found, incomplete strategy% (15809)------------------------------
% 1.43/0.56  % (15809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (15809)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (15809)Memory used [KB]: 10618
% 1.43/0.56  % (15809)Time elapsed: 0.132 s
% 1.43/0.56  % (15809)------------------------------
% 1.43/0.56  % (15809)------------------------------
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f16,plain,(
% 1.43/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f15])).
% 1.43/0.56  fof(f15,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 1.43/0.56    inference(negated_conjecture,[],[f11])).
% 1.43/0.56  fof(f11,conjecture,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 1.43/0.56  fof(f71,plain,(
% 1.43/0.56    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.56    inference(superposition,[],[f70,f42])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f23])).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.43/0.56    inference(subsumption_resolution,[],[f32,f69])).
% 1.43/0.56  fof(f69,plain,(
% 1.43/0.56    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 1.43/0.56    inference(resolution,[],[f68,f30])).
% 1.43/0.56  fof(f68,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,k1_relset_1(X0,X1,sK2))) )),
% 1.43/0.56    inference(resolution,[],[f44,f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    r1_tarski(k6_relat_1(sK1),sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f113,plain,(
% 1.43/0.56    sK1 = k2_relat_1(sK2)),
% 1.43/0.56    inference(forward_demodulation,[],[f107,f34])).
% 1.43/0.56  % (15822)Refutation not found, incomplete strategy% (15822)------------------------------
% 1.43/0.56  % (15822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f4])).
% 1.43/0.56  % (15822)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (15822)Memory used [KB]: 1663
% 1.43/0.56  % (15822)Time elapsed: 0.133 s
% 1.43/0.56  % (15822)------------------------------
% 1.43/0.56  % (15822)------------------------------
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.43/0.56  fof(f107,plain,(
% 1.43/0.56    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))),
% 1.43/0.56    inference(superposition,[],[f34,f102])).
% 1.43/0.56  fof(f102,plain,(
% 1.43/0.56    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 1.43/0.56    inference(subsumption_resolution,[],[f101,f37])).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.43/0.56  fof(f101,plain,(
% 1.43/0.56    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.43/0.56    inference(resolution,[],[f93,f30])).
% 1.43/0.56  fof(f93,plain,(
% 1.43/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(resolution,[],[f92,f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.43/0.56  fof(f92,plain,(
% 1.43/0.56    ~v1_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 1.43/0.56    inference(resolution,[],[f89,f52])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 1.43/0.56    inference(resolution,[],[f51,f40])).
% 1.43/0.56  fof(f40,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(nnf_transformation,[],[f22])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    v5_relat_1(sK2,sK1)),
% 1.43/0.56    inference(resolution,[],[f43,f30])).
% 1.43/0.56  fof(f43,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.43/0.56    inference(pure_predicate_removal,[],[f8])).
% 1.43/0.56  fof(f8,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.43/0.56  fof(f89,plain,(
% 1.43/0.56    ~r1_tarski(k2_relat_1(sK2),sK1) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 1.43/0.56    inference(forward_demodulation,[],[f88,f34])).
% 1.43/0.56  fof(f88,plain,(
% 1.43/0.56    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK2))),sK1)),
% 1.43/0.56    inference(subsumption_resolution,[],[f86,f33])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,plain,(
% 1.43/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.43/0.56    inference(pure_predicate_removal,[],[f7])).
% 1.43/0.56  fof(f7,axiom,(
% 1.43/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.43/0.56  fof(f86,plain,(
% 1.43/0.56    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(sK2))),sK1) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 1.43/0.56    inference(superposition,[],[f85,f38])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f19])).
% 1.43/0.56  fof(f19,plain,(
% 1.43/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f18])).
% 1.43/0.56  fof(f18,plain,(
% 1.43/0.56    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.43/0.56  fof(f85,plain,(
% 1.43/0.56    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(k2_relat_1(sK2)))),
% 1.43/0.56    inference(resolution,[],[f84,f58])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f56,f33])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(superposition,[],[f39,f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f4])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f20])).
% 1.43/0.56  fof(f20,plain,(
% 1.43/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.43/0.56  fof(f84,plain,(
% 1.43/0.56    r1_tarski(sK1,k2_relat_1(sK2))),
% 1.43/0.56    inference(subsumption_resolution,[],[f83,f30])).
% 1.43/0.56  fof(f83,plain,(
% 1.43/0.56    r1_tarski(sK1,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.56    inference(superposition,[],[f81,f42])).
% 1.43/0.56  fof(f81,plain,(
% 1.43/0.56    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 1.43/0.56    inference(resolution,[],[f80,f30])).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,k2_relset_1(X0,X1,sK2))) )),
% 1.43/0.56    inference(resolution,[],[f45,f31])).
% 1.43/0.57  fof(f45,plain,(
% 1.43/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f26])).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (15820)------------------------------
% 1.43/0.57  % (15820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (15820)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (15820)Memory used [KB]: 6140
% 1.43/0.57  % (15820)Time elapsed: 0.125 s
% 1.43/0.57  % (15820)------------------------------
% 1.43/0.57  % (15820)------------------------------
% 1.43/0.57  % (15800)Success in time 0.201 s
%------------------------------------------------------------------------------
