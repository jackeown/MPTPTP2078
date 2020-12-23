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
% DateTime   : Thu Dec  3 13:06:48 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 453 expanded)
%              Number of leaves         :   10 (  91 expanded)
%              Depth                    :   21
%              Number of atoms          :  257 (2536 expanded)
%              Number of equality atoms :   35 ( 446 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f326,f163])).

fof(f163,plain,(
    ! [X4,X3] : r2_relset_1(X3,X4,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f157,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f157,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(X9,k2_zfmisc_1(X10,X11))
      | r2_relset_1(X10,X11,k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f148,f73])).

fof(f73,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f69,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f48])).

fof(f48,plain,(
    k1_xboole_0 = sK6 ),
    inference(resolution,[],[f31,f45])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f45,plain,(
    v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f69,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_xboole_0(X7)
      | r1_tarski(X6,X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f59,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK5(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f35,f36])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f148,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | ~ r1_tarski(X5,k2_zfmisc_1(X2,X3))
      | r2_relset_1(X2,X3,X4,X4) ) ),
    inference(resolution,[],[f116,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_relset_1(X3,X4,X2,X2)
      | ~ r1_tarski(X5,k2_zfmisc_1(X3,X4)) ) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f326,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f282,f307])).

fof(f307,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f304,f31])).

fof(f304,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f244,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f49])).

fof(f61,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X4)
      | v1_xboole_0(X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0),X1)
      | ~ r1_tarski(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f244,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f212,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f212,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f53,f205])).

fof(f205,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f197,f120])).

fof(f120,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f114,f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_relset_1(sK0,sK1,X0,X0) ) ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f197,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f27,f185])).

fof(f185,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f184,f31])).

fof(f184,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f181,f30])).

fof(f181,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 = sK3
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f180,f25])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK2 = sK3
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f179,f94])).

fof(f94,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f82,f29])).

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK2,X2,X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_partfun1(sK2,X2) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_partfun1(sK2,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK2 = sK3
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f140,f92])).

fof(f92,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f91,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_partfun1(sK3,sK0) ),
    inference(resolution,[],[f81,f24])).

fof(f24,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK3,X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK3,X0) ) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | sK2 = sK3 ) ),
    inference(subsumption_resolution,[],[f138,f23])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK2,X0)
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_funct_1(sK2)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f27,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f282,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f208,f269])).

fof(f269,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f266,f31])).

fof(f266,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f243,f62])).

fof(f243,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f211,f46])).

fof(f211,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f52,f205])).

fof(f52,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f25])).

fof(f208,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f27,f205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.18/0.52  % (32391)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.18/0.52  % (32375)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.18/0.52  % (32383)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (32374)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.53  % (32372)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (32372)Refutation not found, incomplete strategy% (32372)------------------------------
% 1.28/0.54  % (32372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (32372)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (32372)Memory used [KB]: 6268
% 1.28/0.54  % (32372)Time elapsed: 0.119 s
% 1.28/0.54  % (32372)------------------------------
% 1.28/0.54  % (32372)------------------------------
% 1.28/0.54  % (32373)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (32393)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.54  % (32369)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (32371)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (32370)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (32374)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % (32386)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.54  % (32380)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (32394)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (32397)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.54  % (32382)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (32385)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.55  % (32395)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.55  % (32396)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.55  % (32389)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.55  % (32387)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.55  % (32376)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.55  % (32379)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.55  % (32384)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.55  % (32388)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.55  % (32390)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.55  % (32377)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.56  % (32378)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.56  % (32381)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.56  % (32394)Refutation not found, incomplete strategy% (32394)------------------------------
% 1.28/0.56  % (32394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (32394)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.56  
% 1.28/0.56  % (32394)Memory used [KB]: 10746
% 1.28/0.56  % (32394)Time elapsed: 0.134 s
% 1.28/0.56  % (32394)------------------------------
% 1.28/0.56  % (32394)------------------------------
% 1.28/0.56  % (32376)Refutation not found, incomplete strategy% (32376)------------------------------
% 1.28/0.56  % (32376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (32390)Refutation not found, incomplete strategy% (32390)------------------------------
% 1.28/0.56  % (32390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % SZS output start Proof for theBenchmark
% 1.28/0.56  fof(f333,plain,(
% 1.28/0.56    $false),
% 1.28/0.56    inference(subsumption_resolution,[],[f326,f163])).
% 1.28/0.56  fof(f163,plain,(
% 1.28/0.56    ( ! [X4,X3] : (r2_relset_1(X3,X4,k1_xboole_0,k1_xboole_0)) )),
% 1.28/0.56    inference(resolution,[],[f157,f57])).
% 1.28/0.56  fof(f57,plain,(
% 1.28/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.28/0.56    inference(duplicate_literal_removal,[],[f56])).
% 1.28/0.56  fof(f56,plain,(
% 1.28/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.28/0.56    inference(resolution,[],[f37,f36])).
% 1.28/0.56  fof(f36,plain,(
% 1.28/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f17])).
% 1.28/0.56  fof(f17,plain,(
% 1.28/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.56    inference(ennf_transformation,[],[f2])).
% 1.28/0.56  fof(f2,axiom,(
% 1.28/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.56  fof(f37,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f17])).
% 1.28/0.56  fof(f157,plain,(
% 1.28/0.56    ( ! [X10,X11,X9] : (~r1_tarski(X9,k2_zfmisc_1(X10,X11)) | r2_relset_1(X10,X11,k1_xboole_0,k1_xboole_0)) )),
% 1.28/0.56    inference(resolution,[],[f148,f73])).
% 1.28/0.56  fof(f73,plain,(
% 1.28/0.56    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.28/0.56    inference(resolution,[],[f71,f57])).
% 1.28/0.56  fof(f71,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.28/0.56    inference(resolution,[],[f69,f49])).
% 1.28/0.56  fof(f49,plain,(
% 1.28/0.56    v1_xboole_0(k1_xboole_0)),
% 1.28/0.56    inference(backward_demodulation,[],[f45,f48])).
% 1.28/0.56  fof(f48,plain,(
% 1.28/0.56    k1_xboole_0 = sK6),
% 1.28/0.56    inference(resolution,[],[f31,f45])).
% 1.28/0.56  fof(f31,plain,(
% 1.28/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.28/0.56    inference(cnf_transformation,[],[f14])).
% 1.28/0.56  fof(f14,plain,(
% 1.28/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.28/0.56    inference(ennf_transformation,[],[f3])).
% 1.28/0.56  fof(f3,axiom,(
% 1.28/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.28/0.56  fof(f45,plain,(
% 1.28/0.56    v1_xboole_0(sK6)),
% 1.28/0.56    inference(cnf_transformation,[],[f4])).
% 1.28/0.56  fof(f4,axiom,(
% 1.28/0.56    ? [X0] : v1_xboole_0(X0)),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 1.28/0.56  fof(f69,plain,(
% 1.28/0.56    ( ! [X6,X8,X7] : (~v1_xboole_0(X7) | r1_tarski(X6,X8) | ~r1_tarski(X6,X7)) )),
% 1.28/0.56    inference(resolution,[],[f59,f33])).
% 1.28/0.56  fof(f33,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f1])).
% 1.28/0.56  fof(f1,axiom,(
% 1.28/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.28/0.56  fof(f59,plain,(
% 1.28/0.56    ( ! [X4,X2,X3] : (r2_hidden(sK5(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 1.28/0.56    inference(resolution,[],[f35,f36])).
% 1.28/0.56  fof(f35,plain,(
% 1.28/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f17])).
% 1.28/0.56  fof(f148,plain,(
% 1.28/0.56    ( ! [X4,X2,X5,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | ~r1_tarski(X5,k2_zfmisc_1(X2,X3)) | r2_relset_1(X2,X3,X4,X4)) )),
% 1.28/0.56    inference(resolution,[],[f116,f38])).
% 1.28/0.56  fof(f38,plain,(
% 1.28/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f6])).
% 1.28/0.56  fof(f6,axiom,(
% 1.28/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.28/0.56  fof(f116,plain,(
% 1.28/0.56    ( ! [X4,X2,X5,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_relset_1(X3,X4,X2,X2) | ~r1_tarski(X5,k2_zfmisc_1(X3,X4))) )),
% 1.28/0.56    inference(resolution,[],[f44,f38])).
% 1.28/0.56  fof(f44,plain,(
% 1.28/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f21])).
% 1.28/0.56  fof(f21,plain,(
% 1.28/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.56    inference(flattening,[],[f20])).
% 1.28/0.56  fof(f20,plain,(
% 1.28/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.28/0.56    inference(ennf_transformation,[],[f7])).
% 1.28/0.56  fof(f7,axiom,(
% 1.28/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.28/0.56  fof(f326,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.28/0.56    inference(backward_demodulation,[],[f282,f307])).
% 1.28/0.56  fof(f307,plain,(
% 1.28/0.56    k1_xboole_0 = sK2),
% 1.28/0.56    inference(resolution,[],[f304,f31])).
% 1.28/0.56  fof(f304,plain,(
% 1.28/0.56    v1_xboole_0(sK2)),
% 1.28/0.56    inference(resolution,[],[f244,f62])).
% 1.28/0.56  fof(f62,plain,(
% 1.28/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.28/0.56    inference(resolution,[],[f61,f49])).
% 1.28/0.56  fof(f61,plain,(
% 1.28/0.56    ( ! [X4,X3] : (~v1_xboole_0(X4) | v1_xboole_0(X3) | ~r1_tarski(X3,X4)) )),
% 1.28/0.56    inference(resolution,[],[f58,f33])).
% 1.28/0.56  fof(f58,plain,(
% 1.28/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0),X1) | ~r1_tarski(X0,X1) | v1_xboole_0(X0)) )),
% 1.28/0.56    inference(resolution,[],[f35,f32])).
% 1.28/0.56  fof(f32,plain,(
% 1.28/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f1])).
% 1.28/0.56  fof(f244,plain,(
% 1.28/0.56    r1_tarski(sK2,k1_xboole_0)),
% 1.28/0.56    inference(forward_demodulation,[],[f212,f46])).
% 1.28/0.56  fof(f46,plain,(
% 1.28/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.28/0.56    inference(equality_resolution,[],[f42])).
% 1.28/0.56  fof(f42,plain,(
% 1.28/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f5])).
% 1.28/0.56  fof(f5,axiom,(
% 1.28/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.28/0.56  fof(f212,plain,(
% 1.28/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.28/0.56    inference(backward_demodulation,[],[f53,f205])).
% 1.28/0.56  fof(f205,plain,(
% 1.28/0.56    k1_xboole_0 = sK1),
% 1.28/0.56    inference(subsumption_resolution,[],[f197,f120])).
% 1.28/0.56  fof(f120,plain,(
% 1.28/0.56    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.28/0.56    inference(resolution,[],[f114,f30])).
% 1.28/0.56  fof(f30,plain,(
% 1.28/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f13,plain,(
% 1.28/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.28/0.56    inference(flattening,[],[f12])).
% 1.28/0.56  fof(f12,plain,(
% 1.28/0.56    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.28/0.56    inference(ennf_transformation,[],[f11])).
% 1.28/0.56  fof(f11,negated_conjecture,(
% 1.28/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.28/0.56    inference(negated_conjecture,[],[f10])).
% 1.28/0.56  fof(f10,conjecture,(
% 1.28/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 1.28/0.56  fof(f114,plain,(
% 1.28/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_relset_1(sK0,sK1,X0,X0)) )),
% 1.28/0.56    inference(resolution,[],[f44,f25])).
% 1.28/0.56  fof(f25,plain,(
% 1.28/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f197,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.28/0.56    inference(superposition,[],[f27,f185])).
% 1.28/0.56  fof(f185,plain,(
% 1.28/0.56    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.28/0.56    inference(resolution,[],[f184,f31])).
% 1.28/0.56  fof(f184,plain,(
% 1.28/0.56    v1_xboole_0(sK1) | sK2 = sK3),
% 1.28/0.56    inference(subsumption_resolution,[],[f181,f30])).
% 1.28/0.56  fof(f181,plain,(
% 1.28/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 = sK3 | v1_xboole_0(sK1)),
% 1.28/0.56    inference(resolution,[],[f180,f25])).
% 1.28/0.56  fof(f180,plain,(
% 1.28/0.56    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | v1_xboole_0(sK1)) )),
% 1.28/0.56    inference(subsumption_resolution,[],[f179,f94])).
% 1.28/0.56  fof(f94,plain,(
% 1.28/0.56    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 1.28/0.56    inference(subsumption_resolution,[],[f93,f30])).
% 1.28/0.56  fof(f93,plain,(
% 1.28/0.56    v1_xboole_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_partfun1(sK2,sK0)),
% 1.28/0.56    inference(resolution,[],[f82,f29])).
% 1.28/0.56  fof(f29,plain,(
% 1.28/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f82,plain,(
% 1.28/0.56    ( ! [X2,X3] : (~v1_funct_2(sK2,X2,X3) | v1_xboole_0(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_partfun1(sK2,X2)) )),
% 1.28/0.56    inference(resolution,[],[f34,f28])).
% 1.28/0.56  fof(f28,plain,(
% 1.28/0.56    v1_funct_1(sK2)),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f34,plain,(
% 1.28/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f16])).
% 1.28/0.56  fof(f16,plain,(
% 1.28/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.28/0.56    inference(flattening,[],[f15])).
% 1.28/0.56  fof(f15,plain,(
% 1.28/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.28/0.56    inference(ennf_transformation,[],[f8])).
% 1.28/0.56  fof(f8,axiom,(
% 1.28/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.28/0.56  fof(f179,plain,(
% 1.28/0.56    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | v1_xboole_0(sK1)) )),
% 1.28/0.56    inference(resolution,[],[f140,f92])).
% 1.28/0.56  fof(f92,plain,(
% 1.28/0.56    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 1.28/0.56    inference(subsumption_resolution,[],[f91,f25])).
% 1.28/0.56  fof(f91,plain,(
% 1.28/0.56    v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_partfun1(sK3,sK0)),
% 1.28/0.56    inference(resolution,[],[f81,f24])).
% 1.28/0.56  fof(f24,plain,(
% 1.28/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f81,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK3,X0)) )),
% 1.28/0.56    inference(resolution,[],[f34,f23])).
% 1.28/0.56  fof(f23,plain,(
% 1.28/0.56    v1_funct_1(sK3)),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f140,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = sK3) )),
% 1.28/0.56    inference(subsumption_resolution,[],[f139,f28])).
% 1.28/0.56  fof(f139,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 1.28/0.56    inference(subsumption_resolution,[],[f138,f23])).
% 1.28/0.56  fof(f138,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | ~v1_partfun1(sK3,X0) | ~v1_funct_1(sK2) | sK2 = sK3) )),
% 1.28/0.56    inference(resolution,[],[f43,f26])).
% 1.28/0.56  fof(f26,plain,(
% 1.28/0.56    r1_partfun1(sK2,sK3)),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f43,plain,(
% 1.28/0.56    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X2) | X2 = X3) )),
% 1.28/0.56    inference(cnf_transformation,[],[f19])).
% 1.28/0.56  fof(f19,plain,(
% 1.28/0.56    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.28/0.56    inference(flattening,[],[f18])).
% 1.28/0.56  fof(f18,plain,(
% 1.28/0.56    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.28/0.56    inference(ennf_transformation,[],[f9])).
% 1.28/0.56  fof(f9,axiom,(
% 1.28/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 1.28/0.56  fof(f27,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.28/0.56    inference(cnf_transformation,[],[f13])).
% 1.28/0.56  fof(f53,plain,(
% 1.28/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.28/0.56    inference(resolution,[],[f39,f30])).
% 1.28/0.56  fof(f39,plain,(
% 1.28/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f6])).
% 1.28/0.56  fof(f282,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)),
% 1.28/0.56    inference(backward_demodulation,[],[f208,f269])).
% 1.28/0.56  fof(f269,plain,(
% 1.28/0.56    k1_xboole_0 = sK3),
% 1.28/0.56    inference(resolution,[],[f266,f31])).
% 1.28/0.56  fof(f266,plain,(
% 1.28/0.56    v1_xboole_0(sK3)),
% 1.28/0.56    inference(resolution,[],[f243,f62])).
% 1.28/0.56  fof(f243,plain,(
% 1.28/0.56    r1_tarski(sK3,k1_xboole_0)),
% 1.28/0.56    inference(forward_demodulation,[],[f211,f46])).
% 1.28/0.56  fof(f211,plain,(
% 1.28/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.28/0.56    inference(backward_demodulation,[],[f52,f205])).
% 1.28/0.56  fof(f52,plain,(
% 1.28/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.28/0.56    inference(resolution,[],[f39,f25])).
% 1.28/0.56  fof(f208,plain,(
% 1.28/0.56    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.28/0.56    inference(backward_demodulation,[],[f27,f205])).
% 1.28/0.56  % SZS output end Proof for theBenchmark
% 1.28/0.56  % (32374)------------------------------
% 1.28/0.56  % (32374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (32374)Termination reason: Refutation
% 1.28/0.56  
% 1.28/0.56  % (32374)Memory used [KB]: 6396
% 1.28/0.56  % (32374)Time elapsed: 0.118 s
% 1.28/0.56  % (32374)------------------------------
% 1.28/0.56  % (32374)------------------------------
% 1.28/0.56  % (32367)Success in time 0.2 s
%------------------------------------------------------------------------------
