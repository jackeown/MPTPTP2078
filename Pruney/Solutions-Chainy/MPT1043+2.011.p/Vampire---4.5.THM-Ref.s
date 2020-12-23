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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 (3168 expanded)
%              Number of leaves         :   11 ( 761 expanded)
%              Depth                    :   32
%              Number of atoms          :  285 (11459 expanded)
%              Number of equality atoms :   18 ( 308 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(subsumption_resolution,[],[f306,f213])).

fof(f213,plain,(
    ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f123,f209])).

fof(f209,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f204,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f204,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(resolution,[],[f202,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

% (31288)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f202,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(resolution,[],[f201,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f200,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f200,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f189,f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f189,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f187,f123])).

fof(f187,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f185,f35])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_xboole_0,sK2))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f166,f50])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k5_partfun1(sK0,k1_xboole_0,sK2))
      | ~ r2_hidden(X0,X1)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f124,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,k1_xboole_0))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k5_partfun1(X0,k1_xboole_0,sK2)) ) ),
    inference(resolution,[],[f100,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).

% (31263)Refutation not found, incomplete strategy% (31263)------------------------------
% (31263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31263)Termination reason: Refutation not found, incomplete strategy

% (31263)Memory used [KB]: 10746
% (31263)Time elapsed: 0.126 s
% (31263)------------------------------
% (31263)------------------------------
fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,k1_xboole_0))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_tarski(X3,k5_partfun1(X0,k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f89,f38])).

fof(f89,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k5_partfun1(X5,k1_xboole_0,X4)))
      | v1_xboole_0(X5)
      | ~ r1_tarski(X4,k2_zfmisc_1(X5,k1_xboole_0))
      | ~ v1_funct_1(X4)
      | ~ r2_hidden(X7,X6) ) ),
    inference(resolution,[],[f87,f45])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f86,f38])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(k5_partfun1(X0,X1,X2))
      | v1_xboole_0(X0) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

fof(f124,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f47,f121])).

fof(f121,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f120,f31])).

fof(f31,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f111,f36])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | k1_xboole_0 = sK1
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f104,f109])).

fof(f109,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f107,f35])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f105,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f103,f75])).

% (31285)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f75,plain,(
    ! [X0] :
      ( v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),X0))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f72,f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1))
      | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),X0))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f40,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),X0),sK0,sK1)
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
      | v1_funct_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f90,f30])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
      | v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_1(X2) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f47,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,(
    ~ r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f31,f121])).

fof(f306,plain,(
    r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f296,f36])).

fof(f296,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f295,f243])).

fof(f243,plain,(
    ! [X0] :
      ( v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(forward_demodulation,[],[f221,f209])).

fof(f221,plain,(
    ! [X0] :
      ( v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0))
      | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) ) ),
    inference(backward_demodulation,[],[f146,f209])).

fof(f146,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0)) ) ),
    inference(forward_demodulation,[],[f130,f121])).

fof(f130,plain,(
    ! [X0] :
      ( v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0))
      | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0) ) ),
    inference(backward_demodulation,[],[f75,f121])).

fof(f295,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) ) ),
    inference(subsumption_resolution,[],[f293,f256])).

fof(f256,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(forward_demodulation,[],[f230,f209])).

fof(f230,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ) ),
    inference(backward_demodulation,[],[f159,f209])).

% (31281)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f159,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
      | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) ) ),
    inference(forward_demodulation,[],[f140,f121])).

fof(f140,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(backward_demodulation,[],[f109,f121])).

fof(f293,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | ~ m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0))
      | ~ v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) ) ),
    inference(resolution,[],[f249,f46])).

% (31280)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f46,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f249,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_xboole_0,k1_xboole_0)
      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) ) ),
    inference(forward_demodulation,[],[f225,f209])).

% (31279)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f225,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)
      | v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f152,f209])).

fof(f152,plain,(
    ! [X0] :
      ( v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0)
      | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) ) ),
    inference(forward_demodulation,[],[f135,f121])).

fof(f135,plain,(
    ! [X0] :
      ( r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)
      | v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),X0),sK0,sK1) ) ),
    inference(backward_demodulation,[],[f94,f121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31276)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (31284)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (31264)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (31268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (31265)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (31273)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31274)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (31262)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (31287)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (31289)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (31266)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (31261)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (31263)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (31267)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (31268)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f306,f213])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    ~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    inference(backward_demodulation,[],[f123,f209])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f204,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f202,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  % (31288)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f201,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f36,f35])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f200,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,X2)) )),
% 0.22/0.54    inference(resolution,[],[f189,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    v1_xboole_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f187,f123])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | v1_xboole_0(sK0)) )),
% 0.22/0.54    inference(resolution,[],[f185,f35])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_xboole_0,sK2)) | v1_xboole_0(sK0)) )),
% 0.22/0.54    inference(resolution,[],[f166,f50])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k5_partfun1(sK0,k1_xboole_0,sK2)) | ~r2_hidden(X0,X1) | v1_xboole_0(sK0)) )),
% 0.22/0.54    inference(resolution,[],[f124,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(sK2,k2_zfmisc_1(X0,k1_xboole_0)) | v1_xboole_0(X0) | ~r2_hidden(X1,X2) | ~r1_tarski(X2,k5_partfun1(X0,k1_xboole_0,sK2))) )),
% 0.22/0.54    inference(resolution,[],[f100,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).
% 0.22/0.54  % (31263)Refutation not found, incomplete strategy% (31263)------------------------------
% 0.22/0.54  % (31263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31263)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31263)Memory used [KB]: 10746
% 0.22/0.54  % (31263)Time elapsed: 0.126 s
% 0.22/0.54  % (31263)------------------------------
% 0.22/0.54  % (31263)------------------------------
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 0.22/0.55    inference(negated_conjecture,[],[f9])).
% 0.22/0.55  fof(f9,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X1) | ~r1_tarski(X1,k2_zfmisc_1(X0,k1_xboole_0)) | v1_xboole_0(X0) | ~r2_hidden(X2,X3) | ~r1_tarski(X3,k5_partfun1(X0,k1_xboole_0,X1))) )),
% 0.22/0.55    inference(resolution,[],[f89,f38])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k5_partfun1(X5,k1_xboole_0,X4))) | v1_xboole_0(X5) | ~r1_tarski(X4,k2_zfmisc_1(X5,k1_xboole_0)) | ~v1_funct_1(X4) | ~r2_hidden(X7,X6)) )),
% 0.22/0.55    inference(resolution,[],[f87,f45])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) | ~v1_funct_1(X0) | v1_xboole_0(X1) | ~r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.22/0.55    inference(resolution,[],[f86,f38])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~v1_funct_1(X0) | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) | v1_xboole_0(X1)) )),
% 0.22/0.55    inference(resolution,[],[f39,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_xboole_0(k5_partfun1(X0,X1,X2)) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 0.22/0.55    inference(backward_demodulation,[],[f47,f121])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    k1_xboole_0 = sK1),
% 0.22/0.55    inference(subsumption_resolution,[],[f120,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f118])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),
% 0.22/0.55    inference(resolution,[],[f111,f36])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | k1_xboole_0 = sK1 | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f104,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(resolution,[],[f107,f35])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.22/0.55    inference(resolution,[],[f105,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k5_partfun1(X1,X2,sK2)) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.55    inference(resolution,[],[f44,f29])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f103,f75])).
% 0.22/0.55  % (31285)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),X0)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(resolution,[],[f73,f35])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | v1_funct_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f72,f30])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k5_partfun1(X1,X2,sK2)) | v1_funct_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f42,f29])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_funct_2(sK0,sK1)) | ~v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2),X0)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(resolution,[],[f40,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),X0),sK0,sK1) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(resolution,[],[f92,f35])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) | v1_funct_2(X0,sK0,sK1)) )),
% 0.22/0.55    inference(resolution,[],[f90,f30])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k5_partfun1(X1,X2,sK2)) | v1_funct_2(X0,X1,X2)) )),
% 0.22/0.55    inference(resolution,[],[f43,f29])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X3,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(X2,k1_funct_2(X0,X1)) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(resolution,[],[f37,f30])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    ~r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),k1_funct_2(sK0,k1_xboole_0))),
% 0.22/0.55    inference(backward_demodulation,[],[f31,f121])).
% 0.22/0.55  fof(f306,plain,(
% 0.22/0.55    r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f304])).
% 0.22/0.55  fof(f304,plain,(
% 0.22/0.55    r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f296,f36])).
% 0.22/0.55  fof(f296,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f295,f243])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f221,f209])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f146,f209])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f130,f121])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0)) | r1_tarski(k5_partfun1(sK0,sK1,sK2),X0)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f75,f121])).
% 0.22/0.55  fof(f295,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f293,f256])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f230,f209])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f159,f209])).
% 0.22/0.55  % (31281)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f140,f121])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f109,f121])).
% 0.22/0.55  fof(f293,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | ~m1_subset_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r2_hidden(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) | ~v1_funct_1(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0))) )),
% 0.22/0.55    inference(resolution,[],[f249,f46])).
% 0.22/0.55  % (31280)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(equality_resolution,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f249,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0),k1_xboole_0,k1_xboole_0) | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f225,f209])).
% 0.22/0.55  % (31279)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK2),X0) | v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f152,f209])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(sK3(k5_partfun1(sK0,k1_xboole_0,sK2),X0),sK0,k1_xboole_0) | r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f135,f121])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k5_partfun1(sK0,k1_xboole_0,sK2),X0) | v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2),X0),sK0,sK1)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f94,f121])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (31268)------------------------------
% 0.22/0.55  % (31268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31268)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (31268)Memory used [KB]: 6396
% 0.22/0.55  % (31268)Time elapsed: 0.085 s
% 0.22/0.55  % (31268)------------------------------
% 0.22/0.55  % (31268)------------------------------
% 0.22/0.55  % (31260)Success in time 0.186 s
%------------------------------------------------------------------------------
