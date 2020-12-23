%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0831+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 613 expanded)
%              Number of leaves         :   10 ( 120 expanded)
%              Depth                    :   33
%              Number of atoms          :  236 (1682 expanded)
%              Number of equality atoms :   47 ( 167 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f62,plain,(
    r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

% (27580)Refutation not found, incomplete strategy% (27580)------------------------------
% (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

% (27580)Termination reason: Refutation not found, incomplete strategy

% (27580)Memory used [KB]: 10618
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

% (27580)Time elapsed: 0.069 s
% (27580)------------------------------
% (27580)------------------------------
fof(f189,plain,(
    ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(backward_demodulation,[],[f72,f187])).

fof(f187,plain,(
    ! [X0] : sK3 = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f169,f62])).

fof(f169,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(superposition,[],[f72,f167])).

fof(f167,plain,(
    ! [X1] :
      ( sK3 = k7_relat_1(sK3,sK2)
      | sK3 = k7_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f165,f156])).

fof(f156,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK3,X2,sK3),sK1)
      | sK3 = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f154,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(sK3,X0,sK3),sK5(sK3,X0,sK3)),sK3)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(sK3,X0,sK3),sK5(sK3,X0,sK3)),sK3)
      | r2_hidden(k4_tarski(sK4(sK3,X0,sK3),sK5(sK3,X0,sK3)),sK3)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,sK3),sK5(X0,X1,sK3)),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,sK3),sK5(X0,X1,sK3)),sK3)
      | k7_relat_1(X0,X1) = sK3 ) ),
    inference(resolution,[],[f29,f52])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f154,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | r2_hidden(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f151,f52])).

fof(f151,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),sK3) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | r2_hidden(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,X5),sK3) ) ),
    inference(superposition,[],[f47,f147])).

fof(f147,plain,(
    sK3 = k7_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f132,f62])).

fof(f132,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | sK3 = k7_relat_1(sK3,sK1) ),
    inference(superposition,[],[f72,f128])).

fof(f128,plain,(
    ! [X3] :
      ( sK3 = k7_relat_1(sK3,sK1)
      | sK3 = k7_relat_1(sK3,X3) ) ),
    inference(resolution,[],[f124,f99])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK3 = k7_relat_1(sK3,sK1) ) ),
    inference(resolution,[],[f114,f24])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | sK3 = k7_relat_1(sK3,sK1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f113,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f113,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | sK3 = k7_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f92,f109])).

fof(f109,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(sK3,X2,sK3),X2)
      | sK3 = k7_relat_1(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f108,f99])).

fof(f108,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(sK3,X2,sK3),X2)
      | ~ r2_hidden(k4_tarski(sK4(sK3,X2,sK3),sK5(sK3,X2,sK3)),sK3)
      | sK3 = k7_relat_1(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f106,f52])).

fof(f106,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(sK3,X2,sK3),X2)
      | ~ r2_hidden(k4_tarski(sK4(sK3,X2,sK3),sK5(sK3,X2,sK3)),sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = k7_relat_1(sK3,X2) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(sK3,X2,sK3),X2)
      | ~ r2_hidden(k4_tarski(sK4(sK3,X2,sK3),sK5(sK3,X2,sK3)),sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = k7_relat_1(sK3,X2)
      | sK3 = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f97,f99])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1,sK3),sK5(X0,X1,sK3)),sK3)
      | ~ r2_hidden(sK4(X0,X1,sK3),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1,sK3),sK5(X0,X1,sK3)),X0)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = sK3 ) ),
    inference(resolution,[],[f27,f52])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,
    ( r2_hidden(sK4(sK3,sK1,sK3),sK1)
    | sK3 = k7_relat_1(sK3,sK1)
    | v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    inference(factoring,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3,X0,sK3),sK1)
      | r2_hidden(sK4(sK3,X0,sK3),X0)
      | sK3 = k7_relat_1(sK3,X0)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f86,f52])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK4(X2,X3,sK3),X3)
      | k7_relat_1(X2,X3) = sK3
      | r2_hidden(sK4(X2,X3,sK3),sK1)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f84,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,sK1)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k2_zfmisc_1(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,sK3),sK5(X0,X1,sK3)),sK3)
      | r2_hidden(sK4(X0,X1,sK3),X1)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = sK3 ) ),
    inference(resolution,[],[f28,f52])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK3 = k7_relat_1(sK3,sK2) ) ),
    inference(resolution,[],[f164,f25])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(X0,X1)
      | sK3 = k7_relat_1(sK3,sK2) ) ),
    inference(resolution,[],[f163,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | sK3 = k7_relat_1(sK3,sK2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f162,f38])).

fof(f162,plain,
    ( v1_xboole_0(sK2)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f159,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK3,X0,sK3),X0)
      | v1_xboole_0(X0)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f109,f33])).

fof(f159,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK3,X0,sK3),sK2)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f156,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f56,f25])).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | m1_subset_1(X1,X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f37,f34])).

fof(f72,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(backward_demodulation,[],[f26,f70])).

fof(f70,plain,(
    ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f26,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
