%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (1606 expanded)
%              Number of leaves         :   15 ( 310 expanded)
%              Depth                    :   22
%              Number of atoms          :  272 (5187 expanded)
%              Number of equality atoms :  120 (2527 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1079,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1078,f761])).

fof(f761,plain,(
    k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f526,f712])).

fof(f712,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f538])).

fof(f538,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f131,f523])).

fof(f523,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f522])).

fof(f522,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f521,f490])).

fof(f490,plain,
    ( sK0 = k2_relat_1(k5_relat_1(sK2,sK1))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f489,f123])).

fof(f123,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f119,f35])).

fof(f35,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

fof(f119,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f489,plain,
    ( k1_xboole_0 = sK0
    | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f487,f72])).

fof(f72,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f57,f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

% (13326)Refutation not found, incomplete strategy% (13326)------------------------------
% (13326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13326)Termination reason: Refutation not found, incomplete strategy

% (13326)Memory used [KB]: 10618
% (13326)Time elapsed: 0.137 s
% (13326)------------------------------
% (13326)------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f487,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f478,f192])).

fof(f192,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),sK0)
      | ~ v1_relat_1(X5)
      | k2_relat_1(X5) = k2_relat_1(k5_relat_1(sK2,X5)) ) ),
    inference(forward_demodulation,[],[f189,f122])).

fof(f122,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f118,f36])).

fof(f36,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f118,plain,(
    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f189,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | ~ r1_tarski(k1_relat_1(X5),k2_relat_1(sK2))
      | k2_relat_1(X5) = k2_relat_1(k5_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f45,f71])).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f478,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f475,f72])).

fof(f475,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f101,f167])).

fof(f167,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f113,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1),k2_zfmisc_1(sK0,sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f78,f38])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f101,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,k2_zfmisc_1(X4,X5))
      | r1_tarski(k1_relat_1(X6),X4)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f97,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k1_relat_1(X6),X4)
      | ~ v1_relat_1(k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X6,k2_zfmisc_1(X4,X5))
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f43,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f521,plain,(
    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f266,f365])).

fof(f365,plain,(
    k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f355,f58])).

fof(f355,plain,(
    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f345,f262])).

fof(f262,plain,(
    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f242,f34])).

fof(f242,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k4_relset_1(X4,X5,sK0,sK0,X3,sK1) = k5_relat_1(X3,sK1) ) ),
    inference(resolution,[],[f59,f38])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f345,plain,(
    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f268,f34])).

fof(f268,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(k4_relset_1(X4,X5,sK0,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X4,sK0))) ) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f266,plain,(
    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f37,f262])).

fof(f37,plain,(
    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f127,f71])).

fof(f127,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f42,f122])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f526,plain,(
    k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f36,f523])).

fof(f1078,plain,(
    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1077,f844])).

fof(f844,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f843,f711])).

fof(f711,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f139,f523])).

fof(f139,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f135,f72])).

fof(f135,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f42,f123])).

fof(f843,plain,(
    k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f802,f725])).

fof(f725,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f279,f712])).

fof(f279,plain,(
    v1_relat_1(k5_relat_1(sK2,sK2)) ),
    inference(resolution,[],[f276,f57])).

fof(f276,plain,(
    m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f272,f258])).

fof(f258,plain,(
    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(resolution,[],[f241,f34])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k4_relset_1(X1,X2,sK0,sK0,X0,sK2) = k5_relat_1(X0,sK2) ) ),
    inference(resolution,[],[f59,f34])).

fof(f272,plain,(
    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f267,f34])).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k4_relset_1(X1,X2,sK0,sK0,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) ) ),
    inference(resolution,[],[f60,f34])).

fof(f802,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f205,f711])).

fof(f205,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(sK1,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[],[f42,f199])).

fof(f199,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f198,f40])).

fof(f40,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f198,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f197,f63])).

fof(f63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f197,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f194,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f65,f39])).

% (13319)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f39,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[],[f47,f61])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f194,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f191,f39])).

fof(f191,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(X4),sK0)
      | ~ v1_relat_1(X4)
      | k2_relat_1(X4) = k2_relat_1(k5_relat_1(sK1,X4)) ) ),
    inference(forward_demodulation,[],[f188,f123])).

fof(f188,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | ~ r1_tarski(k1_relat_1(X4),k2_relat_1(sK1))
      | k2_relat_1(X4) = k2_relat_1(k5_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f45,f72])).

fof(f1077,plain,(
    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1076,f712])).

fof(f1076,plain,(
    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f575,f711])).

fof(f575,plain,(
    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f266,f523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13315)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (13332)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (13337)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (13324)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (13311)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13309)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (13323)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13310)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13313)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (13327)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (13322)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (13329)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (13328)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (13314)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (13318)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (13325)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13326)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (13321)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13312)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13333)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13331)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (13330)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (13335)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (13320)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (13315)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f1079,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f1078,f761])).
% 0.21/0.55  fof(f761,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f526,f712])).
% 0.21/0.55  fof(f712,plain,(
% 0.21/0.55    k1_xboole_0 = sK2),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f538])).
% 0.21/0.55  fof(f538,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.21/0.55    inference(backward_demodulation,[],[f131,f523])).
% 0.21/0.55  fof(f523,plain,(
% 0.21/0.55    k1_xboole_0 = sK0),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f522])).
% 0.21/0.55  fof(f522,plain,(
% 0.21/0.55    sK0 != sK0 | k1_xboole_0 = sK0),
% 0.21/0.55    inference(superposition,[],[f521,f490])).
% 0.21/0.55  fof(f490,plain,(
% 0.21/0.55    sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(forward_demodulation,[],[f489,f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    sK0 = k2_relat_1(sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f119,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f15])).
% 0.21/0.55  fof(f15,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 0.21/0.55    inference(resolution,[],[f58,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.55  fof(f489,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f487,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(resolution,[],[f57,f38])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  % (13326)Refutation not found, incomplete strategy% (13326)------------------------------
% 0.21/0.56  % (13326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13326)Memory used [KB]: 10618
% 0.21/0.56  % (13326)Time elapsed: 0.137 s
% 0.21/0.56  % (13326)------------------------------
% 0.21/0.56  % (13326)------------------------------
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.56  fof(f487,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | ~v1_relat_1(sK1) | k2_relat_1(sK1) = k2_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.56    inference(resolution,[],[f478,f192])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),sK0) | ~v1_relat_1(X5) | k2_relat_1(X5) = k2_relat_1(k5_relat_1(sK2,X5))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f189,f122])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    sK0 = k2_relat_1(sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f118,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f58,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f189,plain,(
% 0.21/0.56    ( ! [X5] : (~v1_relat_1(X5) | ~r1_tarski(k1_relat_1(X5),k2_relat_1(sK2)) | k2_relat_1(X5) = k2_relat_1(k5_relat_1(sK2,X5))) )),
% 0.21/0.56    inference(resolution,[],[f45,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f57,f34])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.56  fof(f478,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0),
% 0.21/0.56    inference(subsumption_resolution,[],[f475,f72])).
% 0.21/0.56  fof(f475,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f469])).
% 0.21/0.56  fof(f469,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.21/0.56    inference(resolution,[],[f101,f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f164])).
% 0.21/0.56  fof(f164,plain,(
% 0.21/0.56    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.21/0.56    inference(resolution,[],[f113,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(sK3(sK1,X1),k2_zfmisc_1(sK0,sK0)) | r1_tarski(sK1,X1)) )),
% 0.21/0.56    inference(resolution,[],[f78,f38])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK3(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 0.21/0.56    inference(resolution,[],[f48,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (~r1_tarski(X6,k2_zfmisc_1(X4,X5)) | r1_tarski(k1_relat_1(X6),X4) | ~v1_relat_1(X6) | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f97,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (r1_tarski(k1_relat_1(X6),X4) | ~v1_relat_1(k2_zfmisc_1(X4,X5)) | ~r1_tarski(X6,k2_zfmisc_1(X4,X5)) | ~v1_relat_1(X6) | k1_xboole_0 = X5 | k1_xboole_0 = X4) )),
% 0.21/0.56    inference(superposition,[],[f43,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.56  fof(f521,plain,(
% 0.21/0.56    sK0 != k2_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.56    inference(superposition,[],[f266,f365])).
% 0.21/0.56  fof(f365,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.56    inference(resolution,[],[f355,f58])).
% 0.21/0.56  fof(f355,plain,(
% 0.21/0.56    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(forward_demodulation,[],[f345,f262])).
% 0.21/0.56  fof(f262,plain,(
% 0.21/0.56    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 0.21/0.56    inference(resolution,[],[f242,f34])).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(X4,X5,sK0,sK0,X3,sK1) = k5_relat_1(X3,sK1)) )),
% 0.21/0.56    inference(resolution,[],[f59,f38])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.21/0.56  fof(f345,plain,(
% 0.21/0.56    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(resolution,[],[f268,f34])).
% 0.21/0.56  fof(f268,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | m1_subset_1(k4_relset_1(X4,X5,sK0,sK0,X3,sK1),k1_zfmisc_1(k2_zfmisc_1(X4,sK0)))) )),
% 0.21/0.56    inference(resolution,[],[f60,f38])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.21/0.56  fof(f266,plain,(
% 0.21/0.56    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 0.21/0.56    inference(backward_demodulation,[],[f37,f262])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK2),
% 0.21/0.56    inference(subsumption_resolution,[],[f127,f71])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.56    inference(superposition,[],[f42,f122])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.56  fof(f526,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.56    inference(backward_demodulation,[],[f36,f523])).
% 0.21/0.56  fof(f1078,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f1077,f844])).
% 0.21/0.56  fof(f844,plain,(
% 0.21/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f843,f711])).
% 0.21/0.56  fof(f711,plain,(
% 0.21/0.56    k1_xboole_0 = sK1),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f542])).
% 0.21/0.56  fof(f542,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.21/0.56    inference(backward_demodulation,[],[f139,f523])).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.56    inference(subsumption_resolution,[],[f135,f72])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | ~v1_relat_1(sK1) | k1_xboole_0 = sK1),
% 0.21/0.56    inference(superposition,[],[f42,f123])).
% 0.21/0.56  fof(f843,plain,(
% 0.21/0.56    k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f802,f725])).
% 0.21/0.56  fof(f725,plain,(
% 0.21/0.56    v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 0.21/0.56    inference(backward_demodulation,[],[f279,f712])).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    v1_relat_1(k5_relat_1(sK2,sK2))),
% 0.21/0.56    inference(resolution,[],[f276,f57])).
% 0.21/0.56  fof(f276,plain,(
% 0.21/0.56    m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(forward_demodulation,[],[f272,f258])).
% 0.21/0.56  fof(f258,plain,(
% 0.21/0.56    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)),
% 0.21/0.56    inference(resolution,[],[f241,f34])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k4_relset_1(X1,X2,sK0,sK0,X0,sK2) = k5_relat_1(X0,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f59,f34])).
% 0.21/0.56  fof(f272,plain,(
% 0.21/0.56    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    inference(resolution,[],[f267,f34])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k4_relset_1(X1,X2,sK0,sK0,X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) )),
% 0.21/0.56    inference(resolution,[],[f60,f34])).
% 0.21/0.56  fof(f802,plain,(
% 0.21/0.56    ~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0)),
% 0.21/0.56    inference(backward_demodulation,[],[f205,f711])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    ~v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f204])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k5_relat_1(sK1,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f42,f199])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k5_relat_1(sK1,k1_xboole_0))),
% 0.21/0.56    inference(forward_demodulation,[],[f198,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK1,k1_xboole_0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f197,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    v1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f46,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.56  fof(f197,plain,(
% 0.21/0.56    ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK1,k1_xboole_0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f194,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f65,f39])).
% 0.21/0.56  % (13319)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.56    inference(superposition,[],[f47,f61])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK1,k1_xboole_0))),
% 0.21/0.56    inference(superposition,[],[f191,f39])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | ~v1_relat_1(X4) | k2_relat_1(X4) = k2_relat_1(k5_relat_1(sK1,X4))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f188,f123])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X4] : (~v1_relat_1(X4) | ~r1_tarski(k1_relat_1(X4),k2_relat_1(sK1)) | k2_relat_1(X4) = k2_relat_1(k5_relat_1(sK1,X4))) )),
% 0.21/0.56    inference(resolution,[],[f45,f72])).
% 0.21/0.56  fof(f1077,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 0.21/0.56    inference(forward_demodulation,[],[f1076,f712])).
% 0.21/0.56  fof(f1076,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK2,k1_xboole_0))),
% 0.21/0.56    inference(forward_demodulation,[],[f575,f711])).
% 0.21/0.56  fof(f575,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK2,sK1))),
% 0.21/0.56    inference(backward_demodulation,[],[f266,f523])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (13315)------------------------------
% 0.21/0.56  % (13315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13315)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (13315)Memory used [KB]: 6908
% 0.21/0.56  % (13315)Time elapsed: 0.112 s
% 0.21/0.56  % (13315)------------------------------
% 0.21/0.56  % (13315)------------------------------
% 0.21/0.56  % (13307)Success in time 0.192 s
%------------------------------------------------------------------------------
