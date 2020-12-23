%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 217 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   19
%              Number of atoms          :  236 ( 667 expanded)
%              Number of equality atoms :   85 ( 193 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7650)Refutation not found, incomplete strategy% (7650)------------------------------
% (7650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7650)Termination reason: Refutation not found, incomplete strategy

% (7650)Memory used [KB]: 10618
% (7650)Time elapsed: 0.200 s
% (7650)------------------------------
% (7650)------------------------------
% (7644)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f672,plain,(
    $false ),
    inference(subsumption_resolution,[],[f668,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f668,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f119,f660])).

fof(f660,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f659,f90])).

fof(f90,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f35])).

fof(f35,plain,
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

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f659,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f658,f221])).

fof(f221,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,X3) ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(backward_demodulation,[],[f193,f208])).

fof(f208,plain,(
    ! [X6] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X6) ),
    inference(resolution,[],[f144,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f144,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k1_xboole_0,X0),X1) ),
    inference(resolution,[],[f121,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f121,plain,(
    ! [X2,X3] : m1_subset_1(k9_relat_1(k1_xboole_0,X3),k1_zfmisc_1(X2)) ),
    inference(backward_demodulation,[],[f112,f116])).

fof(f116,plain,(
    ! [X2,X3,X1] : k9_relat_1(k1_xboole_0,X3) = k7_relset_1(X1,X2,k1_xboole_0,X3) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f112,plain,(
    ! [X2,X3,X1] : m1_subset_1(k7_relset_1(X1,X2,k1_xboole_0,X3),k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

% (7644)Refutation not found, incomplete strategy% (7644)------------------------------
% (7644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7644)Termination reason: Refutation not found, incomplete strategy

% (7644)Memory used [KB]: 1791
% (7644)Time elapsed: 0.199 s
% (7644)------------------------------
% (7644)------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f193,plain,(
    ! [X3] :
      ( r1_xboole_0(k1_xboole_0,X3)
      | k1_xboole_0 != k9_relat_1(k1_xboole_0,X3) ) ),
    inference(backward_demodulation,[],[f105,f191])).

fof(f191,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f130,f98])).

fof(f130,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f129,f82])).

fof(f82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f53,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f129,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

% (7627)Termination reason: Refutation not found, incomplete strategy

% (7627)Memory used [KB]: 1663
% (7627)Time elapsed: 0.188 s
% (7627)------------------------------
% (7627)------------------------------
fof(f37,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f101,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f105,plain,(
    ! [X3] :
      ( k1_xboole_0 != k9_relat_1(k1_xboole_0,X3)
      | r1_xboole_0(k1_relat_1(k1_xboole_0),X3) ) ),
    inference(resolution,[],[f58,f82])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f658,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = k9_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f59,f513])).

fof(f513,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f508,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) ),
    inference(resolution,[],[f90,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f508,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f119,f394])).

fof(f394,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(equality_resolution,[],[f285])).

fof(f285,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f125,f137])).

fof(f137,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f123,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f123,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f122,f90])).

fof(f122,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f100,f56])).

fof(f100,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f73,f47])).

fof(f125,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f124,f90])).

fof(f124,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f49,f115])).

fof(f115,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) ),
    inference(resolution,[],[f75,f47])).

fof(f49,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (7626)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (7649)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (7641)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (7633)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (7634)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (7642)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.58  % (7631)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.58  % (7630)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.58  % (7642)Refutation not found, incomplete strategy% (7642)------------------------------
% 0.21/0.58  % (7642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7636)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.58  % (7635)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.58  % (7642)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (7642)Memory used [KB]: 10618
% 0.21/0.58  % (7642)Time elapsed: 0.149 s
% 0.21/0.58  % (7642)------------------------------
% 0.21/0.58  % (7642)------------------------------
% 0.21/0.59  % (7632)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.60  % (7650)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.60  % (7629)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.60  % (7628)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.61  % (7648)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.61  % (7636)Refutation not found, incomplete strategy% (7636)------------------------------
% 0.21/0.61  % (7636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (7636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (7636)Memory used [KB]: 10746
% 0.21/0.61  % (7636)Time elapsed: 0.181 s
% 0.21/0.61  % (7636)------------------------------
% 0.21/0.61  % (7636)------------------------------
% 0.21/0.61  % (7655)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.61  % (7654)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.61  % (7655)Refutation not found, incomplete strategy% (7655)------------------------------
% 0.21/0.61  % (7655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (7655)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (7655)Memory used [KB]: 1663
% 0.21/0.61  % (7655)Time elapsed: 0.180 s
% 0.21/0.61  % (7655)------------------------------
% 0.21/0.61  % (7655)------------------------------
% 0.21/0.61  % (7640)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.61  % (7652)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.61  % (7645)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.62  % (7647)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.62  % (7646)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.62  % (7637)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.62  % (7643)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.62  % (7627)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.62  % (7633)Refutation found. Thanks to Tanya!
% 0.21/0.62  % SZS status Theorem for theBenchmark
% 0.21/0.62  % (7627)Refutation not found, incomplete strategy% (7627)------------------------------
% 0.21/0.62  % (7627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (7653)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.62  % (7639)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.62  % (7651)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.62  % (7638)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.97/0.63  % SZS output start Proof for theBenchmark
% 1.97/0.63  % (7650)Refutation not found, incomplete strategy% (7650)------------------------------
% 1.97/0.63  % (7650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (7650)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (7650)Memory used [KB]: 10618
% 1.97/0.63  % (7650)Time elapsed: 0.200 s
% 1.97/0.63  % (7650)------------------------------
% 1.97/0.63  % (7650)------------------------------
% 1.97/0.63  % (7644)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.97/0.63  fof(f672,plain,(
% 1.97/0.63    $false),
% 1.97/0.63    inference(subsumption_resolution,[],[f668,f50])).
% 1.97/0.63  fof(f50,plain,(
% 1.97/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f2])).
% 1.97/0.63  fof(f2,axiom,(
% 1.97/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.97/0.63  fof(f668,plain,(
% 1.97/0.63    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.97/0.63    inference(backward_demodulation,[],[f119,f660])).
% 1.97/0.63  fof(f660,plain,(
% 1.97/0.63    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f659,f90])).
% 1.97/0.63  fof(f90,plain,(
% 1.97/0.63    v1_relat_1(sK3)),
% 1.97/0.63    inference(resolution,[],[f72,f47])).
% 1.97/0.63  fof(f47,plain,(
% 1.97/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.97/0.63    inference(cnf_transformation,[],[f36])).
% 1.97/0.63  fof(f36,plain,(
% 1.97/0.63    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f35])).
% 1.97/0.63  fof(f35,plain,(
% 1.97/0.63    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f25,plain,(
% 1.97/0.63    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.97/0.63    inference(flattening,[],[f24])).
% 1.97/0.63  fof(f24,plain,(
% 1.97/0.63    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.97/0.63    inference(ennf_transformation,[],[f21])).
% 1.97/0.63  fof(f21,plain,(
% 1.97/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.97/0.63    inference(pure_predicate_removal,[],[f20])).
% 1.97/0.63  fof(f20,negated_conjecture,(
% 1.97/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.97/0.63    inference(negated_conjecture,[],[f19])).
% 1.97/0.63  fof(f19,conjecture,(
% 1.97/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.97/0.63  fof(f72,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  fof(f31,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f15])).
% 1.97/0.63  fof(f15,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.97/0.63  fof(f659,plain,(
% 1.97/0.63    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f658,f221])).
% 1.97/0.63  fof(f221,plain,(
% 1.97/0.63    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) )),
% 1.97/0.63    inference(trivial_inequality_removal,[],[f217])).
% 1.97/0.63  fof(f217,plain,(
% 1.97/0.63    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X3)) )),
% 1.97/0.63    inference(backward_demodulation,[],[f193,f208])).
% 1.97/0.63  fof(f208,plain,(
% 1.97/0.63    ( ! [X6] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X6)) )),
% 1.97/0.63    inference(resolution,[],[f144,f98])).
% 1.97/0.63  fof(f98,plain,(
% 1.97/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.97/0.63    inference(resolution,[],[f63,f50])).
% 1.97/0.63  fof(f63,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f40])).
% 1.97/0.63  fof(f40,plain,(
% 1.97/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.63    inference(flattening,[],[f39])).
% 1.97/0.63  fof(f39,plain,(
% 1.97/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.63    inference(nnf_transformation,[],[f1])).
% 1.97/0.63  fof(f1,axiom,(
% 1.97/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.97/0.63  fof(f144,plain,(
% 1.97/0.63    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),X1)) )),
% 1.97/0.63    inference(resolution,[],[f121,f67])).
% 1.97/0.63  fof(f67,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f43])).
% 1.97/0.63  fof(f43,plain,(
% 1.97/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.97/0.63    inference(nnf_transformation,[],[f8])).
% 1.97/0.63  fof(f8,axiom,(
% 1.97/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.97/0.63  fof(f121,plain,(
% 1.97/0.63    ( ! [X2,X3] : (m1_subset_1(k9_relat_1(k1_xboole_0,X3),k1_zfmisc_1(X2))) )),
% 1.97/0.63    inference(backward_demodulation,[],[f112,f116])).
% 1.97/0.63  fof(f116,plain,(
% 1.97/0.63    ( ! [X2,X3,X1] : (k9_relat_1(k1_xboole_0,X3) = k7_relset_1(X1,X2,k1_xboole_0,X3)) )),
% 1.97/0.63    inference(resolution,[],[f75,f51])).
% 1.97/0.63  fof(f51,plain,(
% 1.97/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f7])).
% 1.97/0.63  fof(f7,axiom,(
% 1.97/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.97/0.63  fof(f75,plain,(
% 1.97/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f34])).
% 1.97/0.63  fof(f34,plain,(
% 1.97/0.63    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f18])).
% 1.97/0.63  fof(f18,axiom,(
% 1.97/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.97/0.63  fof(f112,plain,(
% 1.97/0.63    ( ! [X2,X3,X1] : (m1_subset_1(k7_relset_1(X1,X2,k1_xboole_0,X3),k1_zfmisc_1(X2))) )),
% 1.97/0.63    inference(resolution,[],[f74,f51])).
% 1.97/0.63  fof(f74,plain,(
% 1.97/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f33])).
% 1.97/0.63  fof(f33,plain,(
% 1.97/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f17])).
% 1.97/0.63  % (7644)Refutation not found, incomplete strategy% (7644)------------------------------
% 1.97/0.63  % (7644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (7644)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (7644)Memory used [KB]: 1791
% 1.97/0.63  % (7644)Time elapsed: 0.199 s
% 1.97/0.63  % (7644)------------------------------
% 1.97/0.63  % (7644)------------------------------
% 1.97/0.63  fof(f17,axiom,(
% 1.97/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.97/0.63  fof(f193,plain,(
% 1.97/0.63    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3) | k1_xboole_0 != k9_relat_1(k1_xboole_0,X3)) )),
% 1.97/0.63    inference(backward_demodulation,[],[f105,f191])).
% 1.97/0.63  fof(f191,plain,(
% 1.97/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.97/0.63    inference(resolution,[],[f130,f98])).
% 1.97/0.63  fof(f130,plain,(
% 1.97/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f129,f82])).
% 1.97/0.63  fof(f82,plain,(
% 1.97/0.63    v1_relat_1(k1_xboole_0)),
% 1.97/0.63    inference(superposition,[],[f53,f80])).
% 1.97/0.63  fof(f80,plain,(
% 1.97/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.97/0.63    inference(equality_resolution,[],[f71])).
% 1.97/0.63  fof(f71,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.97/0.63    inference(cnf_transformation,[],[f45])).
% 1.97/0.63  fof(f45,plain,(
% 1.97/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.97/0.63    inference(flattening,[],[f44])).
% 1.97/0.63  fof(f44,plain,(
% 1.97/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.97/0.63    inference(nnf_transformation,[],[f6])).
% 1.97/0.63  fof(f6,axiom,(
% 1.97/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.97/0.63  fof(f53,plain,(
% 1.97/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f11])).
% 1.97/0.63  fof(f11,axiom,(
% 1.97/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.97/0.63  fof(f129,plain,(
% 1.97/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.97/0.63    inference(resolution,[],[f101,f56])).
% 1.97/0.63  fof(f56,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f37])).
% 1.97/0.63  % (7627)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (7627)Memory used [KB]: 1663
% 1.97/0.63  % (7627)Time elapsed: 0.188 s
% 1.97/0.63  % (7627)------------------------------
% 1.97/0.63  % (7627)------------------------------
% 1.97/0.63  fof(f37,plain,(
% 1.97/0.63    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(nnf_transformation,[],[f27])).
% 1.97/0.63  fof(f27,plain,(
% 1.97/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(ennf_transformation,[],[f10])).
% 1.97/0.63  fof(f10,axiom,(
% 1.97/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.97/0.63  fof(f101,plain,(
% 1.97/0.63    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.97/0.63    inference(resolution,[],[f73,f51])).
% 1.97/0.63  fof(f73,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f32])).
% 1.97/0.63  fof(f32,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f22])).
% 1.97/0.63  fof(f22,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.97/0.63    inference(pure_predicate_removal,[],[f16])).
% 1.97/0.63  fof(f16,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.97/0.63  fof(f105,plain,(
% 1.97/0.63    ( ! [X3] : (k1_xboole_0 != k9_relat_1(k1_xboole_0,X3) | r1_xboole_0(k1_relat_1(k1_xboole_0),X3)) )),
% 1.97/0.63    inference(resolution,[],[f58,f82])).
% 1.97/0.63  fof(f58,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f38])).
% 1.97/0.63  fof(f38,plain,(
% 1.97/0.63    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(nnf_transformation,[],[f28])).
% 1.97/0.63  fof(f28,plain,(
% 1.97/0.63    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(ennf_transformation,[],[f13])).
% 1.97/0.63  fof(f13,axiom,(
% 1.97/0.63    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.97/0.63  fof(f658,plain,(
% 1.97/0.63    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k9_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 1.97/0.63    inference(superposition,[],[f59,f513])).
% 1.97/0.63  fof(f513,plain,(
% 1.97/0.63    k1_xboole_0 = k1_relat_1(sK3)),
% 1.97/0.63    inference(subsumption_resolution,[],[f508,f97])).
% 1.97/0.63  fof(f97,plain,(
% 1.97/0.63    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) )),
% 1.97/0.63    inference(resolution,[],[f90,f55])).
% 1.97/0.63  fof(f55,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f26])).
% 1.97/0.63  fof(f26,plain,(
% 1.97/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(ennf_transformation,[],[f12])).
% 1.97/0.63  fof(f12,axiom,(
% 1.97/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.97/0.63  fof(f508,plain,(
% 1.97/0.63    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.97/0.63    inference(superposition,[],[f119,f394])).
% 1.97/0.63  fof(f394,plain,(
% 1.97/0.63    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.97/0.63    inference(equality_resolution,[],[f285])).
% 1.97/0.63  fof(f285,plain,(
% 1.97/0.63    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 1.97/0.63    inference(superposition,[],[f125,f137])).
% 1.97/0.63  fof(f137,plain,(
% 1.97/0.63    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.97/0.63    inference(resolution,[],[f123,f64])).
% 1.97/0.63  fof(f64,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f42])).
% 1.97/0.63  fof(f42,plain,(
% 1.97/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.97/0.63    inference(flattening,[],[f41])).
% 1.97/0.63  fof(f41,plain,(
% 1.97/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.97/0.63    inference(nnf_transformation,[],[f5])).
% 1.97/0.63  fof(f5,axiom,(
% 1.97/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.97/0.63  fof(f123,plain,(
% 1.97/0.63    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.97/0.63    inference(subsumption_resolution,[],[f122,f90])).
% 1.97/0.63  fof(f122,plain,(
% 1.97/0.63    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 1.97/0.63    inference(resolution,[],[f100,f56])).
% 1.97/0.63  fof(f100,plain,(
% 1.97/0.63    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.97/0.63    inference(resolution,[],[f73,f47])).
% 1.97/0.63  fof(f125,plain,(
% 1.97/0.63    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f124,f90])).
% 1.97/0.63  fof(f124,plain,(
% 1.97/0.63    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.97/0.63    inference(resolution,[],[f60,f46])).
% 1.97/0.63  fof(f46,plain,(
% 1.97/0.63    v1_funct_1(sK3)),
% 1.97/0.63    inference(cnf_transformation,[],[f36])).
% 1.97/0.63  fof(f60,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f30])).
% 1.97/0.63  fof(f30,plain,(
% 1.97/0.63    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(flattening,[],[f29])).
% 1.97/0.63  fof(f29,plain,(
% 1.97/0.63    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.97/0.63    inference(ennf_transformation,[],[f14])).
% 1.97/0.63  fof(f14,axiom,(
% 1.97/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.97/0.63  fof(f59,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f38])).
% 1.97/0.63  fof(f119,plain,(
% 1.97/0.63    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.97/0.63    inference(backward_demodulation,[],[f49,f115])).
% 1.97/0.63  fof(f115,plain,(
% 1.97/0.63    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0)) )),
% 1.97/0.63    inference(resolution,[],[f75,f47])).
% 1.97/0.63  fof(f49,plain,(
% 1.97/0.63    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.97/0.63    inference(cnf_transformation,[],[f36])).
% 1.97/0.63  % SZS output end Proof for theBenchmark
% 1.97/0.63  % (7633)------------------------------
% 1.97/0.63  % (7633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (7633)Termination reason: Refutation
% 1.97/0.63  
% 1.97/0.63  % (7633)Memory used [KB]: 2046
% 1.97/0.63  % (7633)Time elapsed: 0.142 s
% 1.97/0.63  % (7633)------------------------------
% 1.97/0.63  % (7633)------------------------------
% 1.97/0.63  % (7654)Refutation not found, incomplete strategy% (7654)------------------------------
% 1.97/0.63  % (7654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (7654)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (7654)Memory used [KB]: 10746
% 1.97/0.63  % (7654)Time elapsed: 0.182 s
% 1.97/0.63  % (7654)------------------------------
% 1.97/0.63  % (7654)------------------------------
% 1.97/0.63  % (7625)Success in time 0.262 s
%------------------------------------------------------------------------------
