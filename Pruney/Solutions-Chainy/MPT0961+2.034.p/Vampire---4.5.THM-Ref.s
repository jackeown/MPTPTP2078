%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 (1339 expanded)
%              Number of leaves         :   10 ( 284 expanded)
%              Depth                    :   23
%              Number of atoms          :  202 (4342 expanded)
%              Number of equality atoms :   62 ( 774 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(subsumption_resolution,[],[f237,f209])).

fof(f209,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f158,f207])).

fof(f207,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f170,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f170,plain,(
    ! [X9] : ~ r2_hidden(X9,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f144,f151])).

fof(f151,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f132,f28])).

fof(f132,plain,(
    ! [X2] : ~ r2_hidden(X2,sK0) ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f128,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f116,f45])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(backward_demodulation,[],[f83,f112])).

fof(f112,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f111,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f110,f92])).

fof(f92,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f91,f45])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | k1_relat_1(sK0) = k1_relset_1(X0,k2_relat_1(sK0),sK0) ) ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X1)
      | k1_relat_1(sK0) = k1_relset_1(X1,X0,sK0) ) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(sK0),X1)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f110,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f109,f86])).

fof(f86,plain,(
    ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f45])).

fof(f85,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f81,f45])).

fof(f81,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f80,f54])).

fof(f54,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f22,f24])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X0] :
      ( v1_funct_2(sK0,X0,k2_relat_1(sK0))
      | k1_relset_1(X0,k2_relat_1(sK0),sK0) != X0
      | k1_xboole_0 = k2_relat_1(sK0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_relat_1(sK0),X4)
      | k1_relset_1(X5,X4,sK0) != X5
      | v1_funct_2(sK0,X5,X4)
      | k1_xboole_0 = X4
      | ~ r1_tarski(k1_relat_1(sK0),X5) ) ),
    inference(resolution,[],[f42,f80])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k1_xboole_0)
      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f80,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f144,plain,(
    ! [X9] : ~ r2_hidden(X9,k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f137,f134])).

fof(f134,plain,(
    ! [X4] : k1_relat_1(sK0) = k1_relset_1(k1_xboole_0,X4,sK0) ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f36,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f137,plain,(
    ! [X10,X9] : ~ r2_hidden(X9,k1_relset_1(k1_xboole_0,X10,sK0)) ),
    inference(resolution,[],[f128,f71])).

fof(f71,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X8,k1_relset_1(k1_xboole_0,X7,X6)) ) ),
    inference(forward_demodulation,[],[f67,f48])).

fof(f67,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X7)))
      | ~ r2_hidden(X8,k1_relset_1(k1_xboole_0,X7,X6)) ) ),
    inference(resolution,[],[f37,f60])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f158,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f118,f151])).

fof(f118,plain,(
    ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f86,f112])).

fof(f237,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f236,f163])).

fof(f163,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f128,f151])).

fof(f236,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f56,f210])).

fof(f210,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f160,f207])).

fof(f160,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f121,f151])).

fof(f121,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f92,f112])).

fof(f56,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f50,f48])).

fof(f50,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15075)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.46  % (15067)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (15075)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f237,f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f158,f207])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f170,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X9] : (~r2_hidden(X9,k1_relat_1(k1_xboole_0))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f144,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(resolution,[],[f132,f28])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(X2,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f128,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f44,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(resolution,[],[f127,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f45])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f83,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f45])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.21/0.48    inference(resolution,[],[f91,f45])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | k1_relat_1(sK0) = k1_relset_1(X0,k2_relat_1(sK0),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f82,f45])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | k1_relat_1(sK0) = k1_relset_1(X1,X0,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f80,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(sK0),X1) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f35,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f109,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f45])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f45])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f80,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f22,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(sK0,X0,k2_relat_1(sK0)) | k1_relset_1(X0,k2_relat_1(sK0),sK0) != X0 | k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f88,f45])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r1_tarski(k2_relat_1(sK0),X4) | k1_relset_1(X5,X4,sK0) != X5 | v1_funct_2(sK0,X5,X4) | k1_xboole_0 = X4 | ~r1_tarski(k1_relat_1(sK0),X5)) )),
% 0.21/0.48    inference(resolution,[],[f42,f80])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k1_xboole_0) | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.21/0.48    inference(superposition,[],[f80,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X9] : (~r2_hidden(X9,k1_relat_1(sK0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f137,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X4] : (k1_relat_1(sK0) = k1_relset_1(k1_xboole_0,X4,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f128,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 0.21/0.48    inference(superposition,[],[f36,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X10,X9] : (~r2_hidden(X9,k1_relset_1(k1_xboole_0,X10,sK0))) )),
% 0.21/0.48    inference(resolution,[],[f128,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X8,k1_relset_1(k1_xboole_0,X7,X6))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f67,f48])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X7))) | ~r2_hidden(X8,k1_relset_1(k1_xboole_0,X7,X6))) )),
% 0.21/0.48    inference(resolution,[],[f37,f60])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f118,f151])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f86,f112])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f236,f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(backward_demodulation,[],[f128,f151])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f234])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(superposition,[],[f56,f210])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f160,f207])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f121,f151])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f92,f112])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f50,f48])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15075)------------------------------
% 0.21/0.48  % (15075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15075)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15075)Memory used [KB]: 1791
% 0.21/0.48  % (15075)Time elapsed: 0.072 s
% 0.21/0.48  % (15075)------------------------------
% 0.21/0.48  % (15075)------------------------------
% 0.21/0.48  % (15055)Success in time 0.126 s
%------------------------------------------------------------------------------
