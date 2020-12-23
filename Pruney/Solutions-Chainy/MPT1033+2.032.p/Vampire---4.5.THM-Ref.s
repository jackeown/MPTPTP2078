%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 642 expanded)
%              Number of leaves         :    9 ( 120 expanded)
%              Depth                    :   23
%              Number of atoms          :  241 (4080 expanded)
%              Number of equality atoms :   45 ( 710 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f166,f69])).

fof(f69,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f65,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f166,plain,(
    ~ r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f124,f148])).

fof(f148,plain,(
    k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f106,f119])).

fof(f119,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f111,f71])).

fof(f71,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f111,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f30,f102])).

fof(f102,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( sK2 = sK3
    | sK2 = sK3
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f96,f90])).

fof(f90,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | sK2 = sK3
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f87,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f86,f34])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | sK2 = sK3
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f85,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(X19,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(sK1))
      | sK2 = sK3 ) ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f80,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f79,f62])).

fof(f62,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X3)
      | ~ v1_funct_2(sK2,X2,X3)
      | v1_partfun1(sK2,X2) ) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f79,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | v1_partfun1(sK3,sK0) ),
    inference(resolution,[],[f55,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK3,X0,X1)
      | v1_partfun1(sK3,X0) ) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK3,sK0)
    | sK2 = sK3 ),
    inference(resolution,[],[f76,f28])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f75,f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f74,f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_funct_1(X2)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f96,plain,(
    ! [X1] :
      ( r1_tarski(sK3,X1)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f94,f28])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | sK2 = sK3
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f84,f41])).

fof(f84,plain,(
    ! [X17,X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | sK2 = sK3
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,sK1))) ) ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( sK2 = sK3
    | sK2 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f97,f90])).

fof(f97,plain,(
    ! [X2] :
      ( r1_tarski(sK2,X2)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f94,f33])).

fof(f124,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:36:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (23591)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (23591)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (23589)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (23597)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f166,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.53    inference(resolution,[],[f65,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.20/0.53    inference(resolution,[],[f46,f34])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f124,f148])).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    k1_xboole_0 = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f147])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.20/0.53    inference(backward_demodulation,[],[f106,f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    k1_xboole_0 = sK3),
% 0.20/0.53    inference(subsumption_resolution,[],[f111,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.53    inference(resolution,[],[f65,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f10])).
% 0.20/0.53  fof(f10,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK3),
% 0.20/0.53    inference(superposition,[],[f30,f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    sK2 = sK3 | k1_xboole_0 = sK3),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    sK2 = sK3 | sK2 = sK3 | k1_xboole_0 = sK3),
% 0.20/0.53    inference(resolution,[],[f96,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | sK2 = sK3 | k1_xboole_0 = X2) )),
% 0.20/0.53    inference(resolution,[],[f87,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | sK2 = sK3) )),
% 0.20/0.53    inference(resolution,[],[f86,f34])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | sK2 = sK3 | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f85,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X19,X18] : (~r2_hidden(X19,X18) | ~m1_subset_1(X18,k1_zfmisc_1(sK1)) | sK2 = sK3) )),
% 0.20/0.53    inference(resolution,[],[f80,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | sK2 = sK3),
% 0.20/0.53    inference(subsumption_resolution,[],[f79,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f61,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(sK2,sK0)),
% 0.20/0.53    inference(resolution,[],[f56,f33])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3) | ~v1_funct_2(sK2,X2,X3) | v1_partfun1(sK2,X2)) )),
% 0.20/0.53    inference(resolution,[],[f35,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ~v1_partfun1(sK2,sK0) | sK2 = sK3 | v1_xboole_0(sK1)),
% 0.20/0.53    inference(resolution,[],[f78,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f59,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK0,sK1) | v1_partfun1(sK3,sK0)),
% 0.20/0.53    inference(resolution,[],[f55,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK3,X0,X1) | v1_partfun1(sK3,X0)) )),
% 0.20/0.53    inference(resolution,[],[f35,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ~v1_partfun1(sK3,sK0) | ~v1_partfun1(sK2,sK0) | sK2 = sK3),
% 0.20/0.53    inference(subsumption_resolution,[],[f77,f33])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(sK2,sK0) | ~v1_partfun1(sK3,sK0) | sK2 = sK3),
% 0.20/0.53    inference(resolution,[],[f76,f28])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | sK2 = sK3) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f75,f31])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f74,f26])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 0.20/0.53    inference(resolution,[],[f43,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    r1_partfun1(sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X2) | X2 = X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(sK3,X1) | sK2 = sK3) )),
% 0.20/0.53    inference(resolution,[],[f94,f28])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | sK2 = sK3 | r1_tarski(X0,X2)) )),
% 0.20/0.53    inference(resolution,[],[f84,f41])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X17,X15,X16] : (~r2_hidden(X15,X16) | sK2 = sK3 | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,sK1)))) )),
% 0.20/0.53    inference(resolution,[],[f80,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f45,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    sK2 = sK3 | k1_xboole_0 = sK2),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    sK2 = sK3 | sK2 = sK3 | k1_xboole_0 = sK2),
% 0.20/0.53    inference(resolution,[],[f97,f90])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2] : (r1_tarski(sK2,X2) | sK2 = sK3) )),
% 0.20/0.53    inference(resolution,[],[f94,f33])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f30,f119])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (23591)------------------------------
% 0.20/0.53  % (23591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23591)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (23591)Memory used [KB]: 6268
% 0.20/0.53  % (23591)Time elapsed: 0.099 s
% 0.20/0.53  % (23591)------------------------------
% 0.20/0.53  % (23591)------------------------------
% 0.20/0.53  % (23606)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (23584)Success in time 0.168 s
%------------------------------------------------------------------------------
