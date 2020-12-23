%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:31 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 575 expanded)
%              Number of leaves         :   11 ( 129 expanded)
%              Depth                    :   21
%              Number of atoms          :  229 (1787 expanded)
%              Number of equality atoms :   21 ( 341 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(global_subsumption,[],[f23,f77,f103,f144])).

fof(f144,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f138,f103])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f137,f77])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f132,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f132,plain,(
    v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f127,f98])).

fof(f98,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f86,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f85,f79])).

fof(f79,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f73,plain,(
    sK2 = sK5(sK0,sK1,sK2) ),
    inference(resolution,[],[f24,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | sK5(X0,X1,X3) = X3 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sK5(X0,X1,X3) = X3
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f24,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f74,plain,(
    sK0 = k1_relat_1(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f24,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | k1_relat_1(sK5(X0,X1,X3)) = X0 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relat_1(sK5(X0,X1,X3)) = X0
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f82,f78])).

fof(f78,plain,(
    v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f71,plain,(
    v1_relat_1(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f24,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_relat_1(sK5(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_relat_1(sK5(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(resolution,[],[f77,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f127,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f120])).

fof(f120,plain,(
    v1_xboole_0(k2_relat_1(sK2)) ),
    inference(global_subsumption,[],[f23,f77,f103,f119])).

fof(f119,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f100,f103])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_xboole_0(k2_relat_1(sK2))
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f99,f77])).

fof(f99,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f97,f25])).

fof(f97,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f96,f77])).

fof(f96,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2))
    | v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f95,f86])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2))
    | v1_partfun1(sK2,sK0) ),
    inference(resolution,[],[f84,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f84,plain,(
    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f83,f79])).

fof(f83,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f81,f78])).

fof(f81,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f77,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f115,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f115,plain,
    ( r2_hidden(sK11(sK2,sK3(sK0)),k2_relat_1(sK2))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f109,f66])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK3(sK0),sK11(sK2,sK3(sK0))),sK2)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f87,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k4_tarski(X0,sK11(sK2,X0)),sK2) ) ),
    inference(superposition,[],[f69,f79])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f103,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK5(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f24,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X1)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f89,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(k2_relat_1(sK2),X2)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f88,f78])).

fof(f88,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X2)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f26,f79])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f72,plain,(
    v1_funct_1(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f24,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | v1_funct_1(sK5(X0,X1,X3)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK5(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:12:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29362)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (29378)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (29357)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (29361)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.26/0.52  % (29357)Refutation not found, incomplete strategy% (29357)------------------------------
% 1.26/0.52  % (29357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (29357)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (29357)Memory used [KB]: 10618
% 1.26/0.52  % (29357)Time elapsed: 0.093 s
% 1.26/0.52  % (29357)------------------------------
% 1.26/0.52  % (29357)------------------------------
% 1.26/0.52  % (29370)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.26/0.52  % (29358)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.52  % (29359)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.26/0.52  % (29380)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.26/0.52  % (29362)Refutation found. Thanks to Tanya!
% 1.26/0.52  % SZS status Theorem for theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f145,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(global_subsumption,[],[f23,f77,f103,f144])).
% 1.26/0.52  fof(f144,plain,(
% 1.26/0.52    v1_funct_2(sK2,sK0,sK1)),
% 1.26/0.52    inference(resolution,[],[f138,f103])).
% 1.26/0.52  fof(f138,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_funct_2(sK2,sK0,X0)) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f137,f77])).
% 1.26/0.52  fof(f137,plain,(
% 1.26/0.52    ( ! [X0] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_funct_2(sK2,sK0,X0)) )),
% 1.26/0.52    inference(resolution,[],[f132,f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f15,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(flattening,[],[f14])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.26/0.52  fof(f132,plain,(
% 1.26/0.52    v1_partfun1(sK2,sK0)),
% 1.26/0.52    inference(resolution,[],[f127,f98])).
% 1.26/0.52  fof(f98,plain,(
% 1.26/0.52    ~v1_xboole_0(sK0) | v1_partfun1(sK2,sK0)),
% 1.26/0.52    inference(resolution,[],[f86,f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f18])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 1.26/0.52  fof(f86,plain,(
% 1.26/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 1.26/0.52    inference(forward_demodulation,[],[f85,f79])).
% 1.26/0.52  fof(f79,plain,(
% 1.26/0.52    sK0 = k1_relat_1(sK2)),
% 1.26/0.52    inference(forward_demodulation,[],[f74,f73])).
% 1.26/0.52  fof(f73,plain,(
% 1.26/0.52    sK2 = sK5(sK0,sK1,sK2)),
% 1.26/0.52    inference(resolution,[],[f24,f61])).
% 1.26/0.52  fof(f61,plain,(
% 1.26/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | sK5(X0,X1,X3) = X3) )),
% 1.26/0.52    inference(equality_resolution,[],[f41])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (sK5(X0,X1,X3) = X3 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.26/0.52    inference(cnf_transformation,[],[f13])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.26/0.52    inference(ennf_transformation,[],[f12])).
% 1.26/0.52  fof(f12,negated_conjecture,(
% 1.26/0.52    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.26/0.52    inference(negated_conjecture,[],[f11])).
% 1.26/0.52  fof(f11,conjecture,(
% 1.26/0.52    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 1.26/0.52  fof(f74,plain,(
% 1.26/0.52    sK0 = k1_relat_1(sK5(sK0,sK1,sK2))),
% 1.26/0.52    inference(resolution,[],[f24,f60])).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | k1_relat_1(sK5(X0,X1,X3)) = X0) )),
% 1.26/0.52    inference(equality_resolution,[],[f42])).
% 1.26/0.52  fof(f42,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (k1_relat_1(sK5(X0,X1,X3)) = X0 | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f85,plain,(
% 1.26/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.26/0.52    inference(subsumption_resolution,[],[f82,f78])).
% 1.26/0.52  fof(f78,plain,(
% 1.26/0.52    v1_relat_1(sK2)),
% 1.26/0.52    inference(backward_demodulation,[],[f71,f73])).
% 1.26/0.52  fof(f71,plain,(
% 1.26/0.52    v1_relat_1(sK5(sK0,sK1,sK2))),
% 1.26/0.52    inference(resolution,[],[f24,f63])).
% 1.26/0.52  fof(f63,plain,(
% 1.26/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_relat_1(sK5(X0,X1,X3))) )),
% 1.26/0.52    inference(equality_resolution,[],[f39])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (v1_relat_1(sK5(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f82,plain,(
% 1.26/0.52    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.26/0.52    inference(resolution,[],[f77,f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(flattening,[],[f21])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,axiom,(
% 1.26/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.26/0.52  fof(f127,plain,(
% 1.26/0.52    v1_xboole_0(sK0)),
% 1.26/0.52    inference(subsumption_resolution,[],[f126,f120])).
% 1.26/0.52  fof(f120,plain,(
% 1.26/0.52    v1_xboole_0(k2_relat_1(sK2))),
% 1.26/0.52    inference(global_subsumption,[],[f23,f77,f103,f119])).
% 1.26/0.52  fof(f119,plain,(
% 1.26/0.52    v1_xboole_0(k2_relat_1(sK2)) | v1_funct_2(sK2,sK0,sK1)),
% 1.26/0.52    inference(resolution,[],[f100,f103])).
% 1.26/0.52  fof(f100,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(k2_relat_1(sK2)) | v1_funct_2(sK2,sK0,X0)) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f99,f77])).
% 1.26/0.52  fof(f99,plain,(
% 1.26/0.52    ( ! [X0] : (v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_funct_2(sK2,sK0,X0)) )),
% 1.26/0.52    inference(resolution,[],[f97,f25])).
% 1.26/0.52  fof(f97,plain,(
% 1.26/0.52    v1_partfun1(sK2,sK0) | v1_xboole_0(k2_relat_1(sK2))),
% 1.26/0.52    inference(subsumption_resolution,[],[f96,f77])).
% 1.26/0.52  fof(f96,plain,(
% 1.26/0.52    ~v1_funct_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | v1_partfun1(sK2,sK0)),
% 1.26/0.52    inference(subsumption_resolution,[],[f95,f86])).
% 1.26/0.52  fof(f95,plain,(
% 1.26/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | v1_partfun1(sK2,sK0)),
% 1.26/0.52    inference(resolution,[],[f84,f28])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_partfun1(X2,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.26/0.52    inference(flattening,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.26/0.52  fof(f84,plain,(
% 1.26/0.52    v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 1.26/0.52    inference(forward_demodulation,[],[f83,f79])).
% 1.26/0.52  fof(f83,plain,(
% 1.26/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.26/0.52    inference(subsumption_resolution,[],[f81,f78])).
% 1.26/0.52  fof(f81,plain,(
% 1.26/0.52    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.26/0.52    inference(resolution,[],[f77,f29])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f126,plain,(
% 1.26/0.52    v1_xboole_0(sK0) | ~v1_xboole_0(k2_relat_1(sK2))),
% 1.26/0.52    inference(resolution,[],[f115,f32])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.26/0.52  fof(f115,plain,(
% 1.26/0.52    r2_hidden(sK11(sK2,sK3(sK0)),k2_relat_1(sK2)) | v1_xboole_0(sK0)),
% 1.26/0.52    inference(resolution,[],[f109,f66])).
% 1.26/0.52  fof(f66,plain,(
% 1.26/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.26/0.52    inference(equality_resolution,[],[f45])).
% 1.26/0.52  fof(f45,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.26/0.52    inference(cnf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.26/0.52  fof(f109,plain,(
% 1.26/0.52    r2_hidden(k4_tarski(sK3(sK0),sK11(sK2,sK3(sK0))),sK2) | v1_xboole_0(sK0)),
% 1.26/0.52    inference(resolution,[],[f87,f31])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f1])).
% 1.26/0.52  fof(f87,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,sK11(sK2,X0)),sK2)) )),
% 1.26/0.52    inference(superposition,[],[f69,f79])).
% 1.26/0.52  fof(f69,plain,(
% 1.26/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0)) )),
% 1.26/0.52    inference(equality_resolution,[],[f53])).
% 1.26/0.52  fof(f53,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK11(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.26/0.52    inference(cnf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.26/0.52  fof(f103,plain,(
% 1.26/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.26/0.52    inference(resolution,[],[f101,f80])).
% 1.26/0.52  fof(f80,plain,(
% 1.26/0.52    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.26/0.52    inference(forward_demodulation,[],[f75,f73])).
% 1.26/0.52  fof(f75,plain,(
% 1.26/0.52    r1_tarski(k2_relat_1(sK5(sK0,sK1,sK2)),sK1)),
% 1.26/0.52    inference(resolution,[],[f24,f59])).
% 1.26/0.52  fof(f59,plain,(
% 1.26/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X1)) )),
% 1.26/0.52    inference(equality_resolution,[],[f43])).
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X1) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f101,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.26/0.52    inference(resolution,[],[f89,f68])).
% 1.26/0.52  fof(f68,plain,(
% 1.26/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.26/0.52    inference(equality_resolution,[],[f49])).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.26/0.52    inference(cnf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.26/0.52  fof(f89,plain,(
% 1.26/0.52    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK2),X2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f88,f78])).
% 1.26/0.52  fof(f88,plain,(
% 1.26/0.52    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.26/0.52    inference(superposition,[],[f26,f79])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.26/0.52    inference(flattening,[],[f16])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.26/0.52    inference(ennf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.26/0.52  fof(f77,plain,(
% 1.26/0.52    v1_funct_1(sK2)),
% 1.26/0.52    inference(backward_demodulation,[],[f72,f73])).
% 1.26/0.52  fof(f72,plain,(
% 1.26/0.52    v1_funct_1(sK5(sK0,sK1,sK2))),
% 1.26/0.52    inference(resolution,[],[f24,f62])).
% 1.26/0.52  fof(f62,plain,(
% 1.26/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | v1_funct_1(sK5(X0,X1,X3))) )),
% 1.26/0.52    inference(equality_resolution,[],[f40])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK5(X0,X1,X3)) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.26/0.52    inference(cnf_transformation,[],[f13])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (29362)------------------------------
% 1.26/0.52  % (29362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (29362)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (29362)Memory used [KB]: 6268
% 1.26/0.52  % (29362)Time elapsed: 0.103 s
% 1.26/0.52  % (29362)------------------------------
% 1.26/0.52  % (29362)------------------------------
% 1.26/0.52  % (29360)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.26/0.52  % (29356)Success in time 0.161 s
%------------------------------------------------------------------------------
