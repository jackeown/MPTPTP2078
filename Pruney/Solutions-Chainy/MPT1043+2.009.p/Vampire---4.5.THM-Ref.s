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
% DateTime   : Thu Dec  3 13:06:58 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   94 (1636 expanded)
%              Number of leaves         :   10 ( 325 expanded)
%              Depth                    :   40
%              Number of atoms          :  286 (5278 expanded)
%              Number of equality atoms :   24 ( 317 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f212,f157])).

fof(f157,plain,(
    ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f105,f153])).

fof(f153,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f148,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f29,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f148,plain,(
    ! [X1] : r1_tarski(sK0,X1) ),
    inference(resolution,[],[f145,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f144,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f143,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f135,f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f135,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f134,f105])).

fof(f134,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f132,f31])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_xboole_0,sK2))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k5_partfun1(sK0,k1_xboole_0,sK2))
      | ~ r2_hidden(X0,X1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f106,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,k1_xboole_0))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k5_partfun1(X0,k1_xboole_0,sK2)) ) ),
    inference(resolution,[],[f76,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0))
      | v1_xboole_0(X1)
      | ~ r2_hidden(X2,X3)
      | ~ r1_tarski(X3,k5_partfun1(X1,k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f74,f33])).

fof(f74,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k5_partfun1(X4,k1_xboole_0,X5)))
      | ~ v1_funct_1(X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X4,k1_xboole_0))
      | v1_xboole_0(X4)
      | ~ r2_hidden(X7,X6) ) ),
    inference(resolution,[],[f72,f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f71,f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k5_partfun1(X0,k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f106,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f45,f103])).

fof(f103,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f102,f24])).

fof(f24,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f98,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | k1_xboole_0 = sK1
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f97,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f96,f22])).

fof(f96,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f93,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(k5_partfun1(X1,X2,X0),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k5_partfun1(X1,X2,X0),X3) ) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f92,f23])).

fof(f92,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK3(k5_partfun1(X0,X1,sK2),X2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k5_partfun1(X0,X1,sK2),X2) ) ),
    inference(resolution,[],[f58,f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(X2) ) ),
    inference(resolution,[],[f38,f22])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),X0))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) ) ),
    inference(resolution,[],[f82,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),X0),sK0,sK1)
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f80,f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(sK3(k5_partfun1(X0,X1,sK2),X2),X0,X1)
      | r1_tarski(k5_partfun1(X0,X1,sK2),X2) ) ),
    inference(resolution,[],[f75,f22])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(sK3(k5_partfun1(X1,X2,X0),X3),X1,X2)
      | r1_tarski(k5_partfun1(X1,X2,X0),X3) ) ),
    inference(resolution,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f105,plain,(
    ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f24,f103])).

fof(f212,plain,(
    r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f208,f32])).

fof(f208,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f207,f156])).

fof(f156,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f104,f153])).

fof(f104,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f23,f103])).

fof(f207,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(subsumption_resolution,[],[f206,f22])).

fof(f206,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(resolution,[],[f203,f79])).

fof(f203,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f202,f156])).

fof(f202,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(resolution,[],[f199,f61])).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ) ),
    inference(resolution,[],[f180,f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f180,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_xboole_0,k1_xboole_0)
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(forward_demodulation,[],[f163,f153])).

fof(f163,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_xboole_0,k1_xboole_0)
      | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) ) ),
    inference(backward_demodulation,[],[f116,f153])).

fof(f116,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f111,f103])).

fof(f111,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0)
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(backward_demodulation,[],[f82,f103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (22336)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.49  % (22318)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (22318)Refutation not found, incomplete strategy% (22318)------------------------------
% 0.22/0.49  % (22318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22318)Memory used [KB]: 10618
% 0.22/0.50  % (22318)Time elapsed: 0.064 s
% 0.22/0.50  % (22318)------------------------------
% 0.22/0.50  % (22318)------------------------------
% 0.22/0.51  % (22310)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (22335)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (22312)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (22327)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (22317)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (22324)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (22333)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (22334)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (22308)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (22311)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (22309)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (22338)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (22314)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (22319)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (22340)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (22319)Refutation not found, incomplete strategy% (22319)------------------------------
% 0.22/0.55  % (22319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22319)Memory used [KB]: 10618
% 0.22/0.55  % (22319)Time elapsed: 0.135 s
% 0.22/0.55  % (22319)------------------------------
% 0.22/0.55  % (22319)------------------------------
% 0.22/0.55  % (22325)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (22337)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (22326)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.55  % (22313)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.55  % (22332)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.55  % (22328)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.55  % (22330)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.56  % (22315)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.56  % (22316)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.56  % (22320)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (22331)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (22321)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.57  % (22314)Refutation found. Thanks to Tanya!
% 1.48/0.57  % SZS status Theorem for theBenchmark
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f213,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(subsumption_resolution,[],[f212,f157])).
% 1.48/0.57  fof(f157,plain,(
% 1.48/0.57    ~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.48/0.57    inference(backward_demodulation,[],[f105,f153])).
% 1.48/0.57  fof(f153,plain,(
% 1.48/0.57    k1_xboole_0 = sK0),
% 1.48/0.57    inference(resolution,[],[f148,f49])).
% 1.48/0.57  fof(f49,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.48/0.57    inference(resolution,[],[f29,f26])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f4])).
% 1.48/0.57  fof(f4,axiom,(
% 1.48/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.57  fof(f29,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f3])).
% 1.48/0.57  fof(f3,axiom,(
% 1.48/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.57  fof(f148,plain,(
% 1.48/0.57    ( ! [X1] : (r1_tarski(sK0,X1)) )),
% 1.48/0.57    inference(resolution,[],[f145,f42])).
% 1.48/0.57  fof(f42,plain,(
% 1.48/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.57    inference(equality_resolution,[],[f28])).
% 1.48/0.57  fof(f28,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f3])).
% 1.48/0.57  fof(f145,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(resolution,[],[f144,f31])).
% 1.48/0.57  fof(f31,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,plain,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.57    inference(ennf_transformation,[],[f1])).
% 1.48/0.57  fof(f1,axiom,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.57  fof(f144,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,sK0)) )),
% 1.48/0.57    inference(resolution,[],[f143,f33])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f5])).
% 1.48/0.57  fof(f5,axiom,(
% 1.48/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.57  fof(f143,plain,(
% 1.48/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,X2)) )),
% 1.48/0.57    inference(resolution,[],[f135,f41])).
% 1.48/0.57  fof(f41,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f21])).
% 1.48/0.57  fof(f21,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f6])).
% 1.48/0.57  fof(f6,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.48/0.57  fof(f135,plain,(
% 1.48/0.57    v1_xboole_0(sK0)),
% 1.48/0.57    inference(resolution,[],[f134,f105])).
% 1.48/0.57  fof(f134,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | v1_xboole_0(sK0)) )),
% 1.48/0.57    inference(resolution,[],[f132,f31])).
% 1.48/0.57  fof(f132,plain,(
% 1.48/0.57    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_xboole_0,sK2)) | v1_xboole_0(sK0)) )),
% 1.48/0.57    inference(resolution,[],[f117,f42])).
% 1.48/0.57  fof(f117,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k5_partfun1(sK0,k1_xboole_0,sK2)) | ~r2_hidden(X0,X1) | v1_xboole_0(sK0)) )),
% 1.48/0.57    inference(resolution,[],[f106,f77])).
% 1.48/0.57  fof(f77,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~r1_tarski(sK2,k2_zfmisc_1(X0,k1_xboole_0)) | v1_xboole_0(X0) | ~r2_hidden(X1,X2) | ~r1_tarski(X2,k5_partfun1(X0,k1_xboole_0,sK2))) )),
% 1.48/0.57    inference(resolution,[],[f76,f22])).
% 1.48/0.57  fof(f22,plain,(
% 1.48/0.57    v1_funct_1(sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f13])).
% 1.48/0.57  fof(f13,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.48/0.57    inference(flattening,[],[f12])).
% 1.48/0.57  fof(f12,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f11])).
% 1.48/0.57  fof(f11,negated_conjecture,(
% 1.48/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.48/0.57    inference(negated_conjecture,[],[f10])).
% 1.48/0.57  fof(f10,conjecture,(
% 1.48/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).
% 1.48/0.57  fof(f76,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0)) | v1_xboole_0(X1) | ~r2_hidden(X2,X3) | ~r1_tarski(X3,k5_partfun1(X1,k1_xboole_0,X0))) )),
% 1.48/0.57    inference(resolution,[],[f74,f33])).
% 1.48/0.57  fof(f74,plain,(
% 1.48/0.57    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k5_partfun1(X4,k1_xboole_0,X5))) | ~v1_funct_1(X5) | ~r1_tarski(X5,k2_zfmisc_1(X4,k1_xboole_0)) | v1_xboole_0(X4) | ~r2_hidden(X7,X6)) )),
% 1.48/0.57    inference(resolution,[],[f72,f41])).
% 1.48/0.57  fof(f72,plain,(
% 1.48/0.57    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) | v1_xboole_0(X1) | ~v1_funct_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.48/0.57    inference(resolution,[],[f71,f33])).
% 1.48/0.57  fof(f71,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_1(X1) | v1_xboole_0(X0) | v1_xboole_0(k5_partfun1(X0,k1_xboole_0,X1))) )),
% 1.48/0.57    inference(resolution,[],[f35,f25])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    v1_xboole_0(k1_xboole_0)),
% 1.48/0.57    inference(cnf_transformation,[],[f2])).
% 1.48/0.57  fof(f2,axiom,(
% 1.48/0.57    v1_xboole_0(k1_xboole_0)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.57  fof(f35,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(k5_partfun1(X0,X1,X2))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.48/0.57    inference(flattening,[],[f15])).
% 1.48/0.57  fof(f15,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.48/0.57    inference(ennf_transformation,[],[f7])).
% 1.48/0.57  fof(f7,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).
% 1.48/0.57  fof(f106,plain,(
% 1.48/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.48/0.57    inference(backward_demodulation,[],[f45,f103])).
% 1.48/0.57  fof(f103,plain,(
% 1.48/0.57    k1_xboole_0 = sK1),
% 1.48/0.57    inference(subsumption_resolution,[],[f102,f24])).
% 1.48/0.57  fof(f24,plain,(
% 1.48/0.57    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 1.48/0.57    inference(cnf_transformation,[],[f13])).
% 1.48/0.57  fof(f102,plain,(
% 1.48/0.57    k1_xboole_0 = sK1 | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f99])).
% 1.48/0.57  fof(f99,plain,(
% 1.48/0.57    k1_xboole_0 = sK1 | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 1.48/0.57    inference(resolution,[],[f98,f32])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f98,plain,(
% 1.48/0.57    ( ! [X0] : (r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | k1_xboole_0 = sK1 | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f97,f23])).
% 1.48/0.57  fof(f23,plain,(
% 1.48/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.57    inference(cnf_transformation,[],[f13])).
% 1.48/0.57  fof(f97,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f96,f22])).
% 1.48/0.57  fof(f96,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f94])).
% 1.48/0.57  fof(f94,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 1.48/0.57    inference(resolution,[],[f93,f79])).
% 1.48/0.57  fof(f79,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(k5_partfun1(X1,X2,X0),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k5_partfun1(X1,X2,X0),X3)) )),
% 1.48/0.57    inference(resolution,[],[f40,f31])).
% 1.48/0.57  fof(f40,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f20])).
% 1.48/0.57  fof(f20,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.48/0.57    inference(flattening,[],[f19])).
% 1.48/0.57  fof(f19,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f9])).
% 1.48/0.57  fof(f9,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 1.48/0.57  fof(f93,plain,(
% 1.48/0.57    ( ! [X0] : (~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f92,f23])).
% 1.48/0.57  fof(f92,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f91])).
% 1.48/0.57  fof(f91,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 1.48/0.57    inference(resolution,[],[f84,f61])).
% 1.48/0.57  fof(f61,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (v1_funct_1(sK3(k5_partfun1(X0,X1,sK2),X2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k5_partfun1(X0,X1,sK2),X2)) )),
% 1.48/0.57    inference(resolution,[],[f58,f31])).
% 1.48/0.57  fof(f58,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(X2)) )),
% 1.48/0.57    inference(resolution,[],[f38,f22])).
% 1.48/0.57  fof(f38,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f20])).
% 1.48/0.57  fof(f84,plain,(
% 1.48/0.57    ( ! [X0] : (~v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),X0)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))) )),
% 1.48/0.57    inference(resolution,[],[f82,f36])).
% 1.48/0.57  fof(f36,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f18])).
% 1.48/0.57  fof(f18,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.57    inference(flattening,[],[f17])).
% 1.48/0.57  fof(f17,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f8])).
% 1.48/0.57  fof(f8,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 1.48/0.57  fof(f82,plain,(
% 1.48/0.57    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),X0),sK0,sK1) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 1.48/0.57    inference(resolution,[],[f80,f23])).
% 1.48/0.57  fof(f80,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK3(k5_partfun1(X0,X1,sK2),X2),X0,X1) | r1_tarski(k5_partfun1(X0,X1,sK2),X2)) )),
% 1.48/0.57    inference(resolution,[],[f75,f22])).
% 1.48/0.57  fof(f75,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(sK3(k5_partfun1(X1,X2,X0),X3),X1,X2) | r1_tarski(k5_partfun1(X1,X2,X0),X3)) )),
% 1.48/0.57    inference(resolution,[],[f39,f31])).
% 1.48/0.57  fof(f39,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_2(X3,X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f20])).
% 1.48/0.57  fof(f45,plain,(
% 1.48/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.48/0.57    inference(resolution,[],[f34,f23])).
% 1.48/0.57  fof(f34,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f5])).
% 1.48/0.57  fof(f105,plain,(
% 1.48/0.57    ~r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))),
% 1.48/0.57    inference(backward_demodulation,[],[f24,f103])).
% 1.48/0.57  fof(f212,plain,(
% 1.48/0.57    r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f209])).
% 1.48/0.57  fof(f209,plain,(
% 1.48/0.57    r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 1.48/0.57    inference(resolution,[],[f208,f32])).
% 1.48/0.57  fof(f208,plain,(
% 1.48/0.57    ( ! [X0] : (r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f207,f156])).
% 1.48/0.57  fof(f156,plain,(
% 1.48/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.48/0.57    inference(backward_demodulation,[],[f104,f153])).
% 1.48/0.57  fof(f104,plain,(
% 1.48/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.48/0.57    inference(backward_demodulation,[],[f23,f103])).
% 1.48/0.57  fof(f207,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f206,f22])).
% 1.48/0.57  fof(f206,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f204])).
% 1.48/0.57  fof(f204,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 1.48/0.57    inference(resolution,[],[f203,f79])).
% 1.48/0.57  fof(f203,plain,(
% 1.48/0.57    ( ! [X0] : (~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f202,f156])).
% 1.48/0.57  fof(f202,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f201])).
% 1.48/0.57  fof(f201,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 1.48/0.57    inference(resolution,[],[f199,f61])).
% 1.48/0.57  fof(f199,plain,(
% 1.48/0.57    ( ! [X0] : (~v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))) )),
% 1.48/0.57    inference(resolution,[],[f180,f44])).
% 1.48/0.57  fof(f44,plain,(
% 1.48/0.57    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))) )),
% 1.48/0.57    inference(equality_resolution,[],[f37])).
% 1.48/0.57  fof(f37,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f18])).
% 1.48/0.57  fof(f180,plain,(
% 1.48/0.57    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_xboole_0,k1_xboole_0) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f163,f153])).
% 1.48/0.57  fof(f163,plain,(
% 1.48/0.57    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_xboole_0,k1_xboole_0) | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)) )),
% 1.48/0.57    inference(backward_demodulation,[],[f116,f153])).
% 1.48/0.57  fof(f116,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f111,f103])).
% 1.48/0.57  fof(f111,plain,(
% 1.48/0.57    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 1.48/0.57    inference(backward_demodulation,[],[f82,f103])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (22314)------------------------------
% 1.48/0.57  % (22314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (22314)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (22314)Memory used [KB]: 6396
% 1.48/0.57  % (22314)Time elapsed: 0.138 s
% 1.48/0.57  % (22314)------------------------------
% 1.48/0.57  % (22314)------------------------------
% 1.62/0.57  % (22306)Success in time 0.205 s
%------------------------------------------------------------------------------
