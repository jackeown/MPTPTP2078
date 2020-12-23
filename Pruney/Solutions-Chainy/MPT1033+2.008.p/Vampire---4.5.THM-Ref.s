%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:43 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 357 expanded)
%              Number of leaves         :   13 ( 109 expanded)
%              Depth                    :   22
%              Number of atoms          :  293 (2913 expanded)
%              Number of equality atoms :   65 ( 614 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5558)Refutation not found, incomplete strategy% (5558)------------------------------
% (5558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5558)Termination reason: Refutation not found, incomplete strategy

% (5558)Memory used [KB]: 10618
% (5558)Time elapsed: 0.132 s
% (5558)------------------------------
% (5558)------------------------------
fof(f421,plain,(
    $false ),
    inference(subsumption_resolution,[],[f420,f109])).

fof(f109,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f94,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f420,plain,(
    ~ r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f401,f353])).

fof(f353,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f350,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f350,plain,(
    ! [X5] : ~ r2_hidden(X5,sK2) ),
    inference(resolution,[],[f313,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f85,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f313,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f300,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f300,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f51,f298])).

fof(f298,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f265,f110])).

fof(f110,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f94,f51])).

fof(f265,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f260])).

fof(f260,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f255,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f255,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f252,f51])).

fof(f252,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f251,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f251,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | sK2 = sK3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f249,f157])).

fof(f157,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f151,f51])).

fof(f151,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f147,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f249,plain,(
    ! [X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK2,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f247,f166])).

fof(f166,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f160,f54])).

fof(f160,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f148,f53])).

fof(f53,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f148,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK3,X2,X3)
      | v1_partfun1(sK3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f70,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK3,X0)
      | sK2 = sK3
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f246,f49])).

fof(f246,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f245,f52])).

fof(f245,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f83,f55])).

fof(f55,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f401,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0) ),
    inference(superposition,[],[f57,f396])).

fof(f396,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f393,f66])).

% (5561)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f393,plain,(
    ! [X5] : ~ r2_hidden(X5,sK3) ),
    inference(resolution,[],[f314,f103])).

fof(f314,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f302,f87])).

fof(f302,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f54,f298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:25:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (5557)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (5556)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (5557)Refutation not found, incomplete strategy% (5557)------------------------------
% 0.22/0.53  % (5557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (5572)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.33/0.54  % (5565)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.33/0.55  % (5570)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.33/0.55  % (5573)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.33/0.55  % (5562)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.33/0.55  % (5557)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (5557)Memory used [KB]: 6268
% 1.33/0.55  % (5557)Time elapsed: 0.108 s
% 1.33/0.55  % (5557)------------------------------
% 1.33/0.55  % (5557)------------------------------
% 1.33/0.55  % (5552)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.33/0.55  % (5564)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.33/0.55  % (5554)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.53/0.56  % (5552)Refutation not found, incomplete strategy% (5552)------------------------------
% 1.53/0.56  % (5552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (5555)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.53/0.56  % (5553)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.56  % (5565)Refutation not found, incomplete strategy% (5565)------------------------------
% 1.53/0.56  % (5565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (5565)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (5565)Memory used [KB]: 6396
% 1.53/0.56  % (5565)Time elapsed: 0.133 s
% 1.53/0.56  % (5565)------------------------------
% 1.53/0.56  % (5565)------------------------------
% 1.53/0.56  % (5558)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.53/0.56  % (5573)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % SZS output start Proof for theBenchmark
% 1.53/0.56  % (5558)Refutation not found, incomplete strategy% (5558)------------------------------
% 1.53/0.56  % (5558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (5558)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (5558)Memory used [KB]: 10618
% 1.53/0.56  % (5558)Time elapsed: 0.132 s
% 1.53/0.56  % (5558)------------------------------
% 1.53/0.56  % (5558)------------------------------
% 1.53/0.56  fof(f421,plain,(
% 1.53/0.56    $false),
% 1.53/0.56    inference(subsumption_resolution,[],[f420,f109])).
% 1.53/0.56  fof(f109,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 1.53/0.56    inference(resolution,[],[f94,f59])).
% 1.53/0.56  fof(f59,plain,(
% 1.53/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f5])).
% 1.53/0.56  fof(f5,axiom,(
% 1.53/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.53/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.53/0.56  fof(f94,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 1.53/0.56    inference(condensation,[],[f86])).
% 1.53/0.56  fof(f86,plain,(
% 1.53/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(flattening,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.53/0.57    inference(ennf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.53/0.57  fof(f420,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)),
% 1.53/0.57    inference(forward_demodulation,[],[f401,f353])).
% 1.53/0.57  fof(f353,plain,(
% 1.53/0.57    k1_xboole_0 = sK2),
% 1.53/0.57    inference(resolution,[],[f350,f66])).
% 1.53/0.57  fof(f66,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f45])).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.53/0.57    inference(ennf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,axiom,(
% 1.53/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.53/0.57  fof(f350,plain,(
% 1.53/0.57    ( ! [X5] : (~r2_hidden(X5,sK2)) )),
% 1.53/0.57    inference(resolution,[],[f313,f103])).
% 1.53/0.57  fof(f103,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.53/0.57    inference(resolution,[],[f85,f58])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    v1_xboole_0(k1_xboole_0)),
% 1.53/0.57    inference(cnf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    v1_xboole_0(k1_xboole_0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.53/0.57  fof(f85,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.53/0.57  fof(f313,plain,(
% 1.53/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.53/0.57    inference(forward_demodulation,[],[f300,f87])).
% 1.53/0.57  fof(f87,plain,(
% 1.53/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.53/0.57    inference(equality_resolution,[],[f73])).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.53/0.57    inference(cnf_transformation,[],[f47])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.53/0.57    inference(flattening,[],[f46])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.53/0.57    inference(nnf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.53/0.57  fof(f300,plain,(
% 1.53/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.53/0.57    inference(superposition,[],[f51,f298])).
% 1.53/0.57  fof(f298,plain,(
% 1.53/0.57    k1_xboole_0 = sK1),
% 1.53/0.57    inference(subsumption_resolution,[],[f265,f110])).
% 1.53/0.57  fof(f110,plain,(
% 1.53/0.57    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.53/0.57    inference(resolution,[],[f94,f51])).
% 1.53/0.57  fof(f265,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.53/0.57    inference(superposition,[],[f57,f260])).
% 1.53/0.57  fof(f260,plain,(
% 1.53/0.57    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.53/0.57    inference(resolution,[],[f255,f62])).
% 1.53/0.57  fof(f62,plain,(
% 1.53/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f22])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.53/0.57  fof(f255,plain,(
% 1.53/0.57    v1_xboole_0(sK1) | sK2 = sK3),
% 1.53/0.57    inference(subsumption_resolution,[],[f252,f51])).
% 1.53/0.57  fof(f252,plain,(
% 1.53/0.57    sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 1.53/0.57    inference(resolution,[],[f251,f54])).
% 1.53/0.57  fof(f54,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/0.57    inference(flattening,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.53/0.57    inference(ennf_transformation,[],[f18])).
% 1.53/0.57  fof(f18,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.53/0.57    inference(negated_conjecture,[],[f17])).
% 1.53/0.57  fof(f17,conjecture,(
% 1.53/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 1.53/0.57  fof(f251,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | v1_xboole_0(sK1)) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f249,f157])).
% 1.53/0.57  fof(f157,plain,(
% 1.53/0.57    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 1.53/0.57    inference(subsumption_resolution,[],[f151,f51])).
% 1.53/0.57  fof(f151,plain,(
% 1.53/0.57    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 1.53/0.57    inference(resolution,[],[f147,f50])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f147,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.53/0.57    inference(resolution,[],[f70,f49])).
% 1.53/0.57  fof(f49,plain,(
% 1.53/0.57    v1_funct_1(sK2)),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f27])).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.53/0.57    inference(flattening,[],[f26])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,axiom,(
% 1.53/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.53/0.57  fof(f249,plain,(
% 1.53/0.57    ( ! [X1] : (sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | v1_xboole_0(sK1)) )),
% 1.53/0.57    inference(resolution,[],[f247,f166])).
% 1.53/0.57  fof(f166,plain,(
% 1.53/0.57    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 1.53/0.57    inference(subsumption_resolution,[],[f160,f54])).
% 1.53/0.57  fof(f160,plain,(
% 1.53/0.57    v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 1.53/0.57    inference(resolution,[],[f148,f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f148,plain,(
% 1.53/0.57    ( ! [X2,X3] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3)) )),
% 1.53/0.57    inference(resolution,[],[f70,f52])).
% 1.53/0.57  fof(f52,plain,(
% 1.53/0.57    v1_funct_1(sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f247,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | sK2 = sK3 | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f246,f49])).
% 1.53/0.57  fof(f246,plain,(
% 1.53/0.57    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f245,f52])).
% 1.53/0.57  fof(f245,plain,(
% 1.53/0.57    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 1.53/0.57    inference(resolution,[],[f83,f55])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    r1_partfun1(sK2,sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f83,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f34])).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.53/0.57    inference(flattening,[],[f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.53/0.57    inference(ennf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f401,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK1,sK2,k1_xboole_0)),
% 1.53/0.57    inference(superposition,[],[f57,f396])).
% 1.53/0.57  fof(f396,plain,(
% 1.53/0.57    k1_xboole_0 = sK3),
% 1.53/0.57    inference(resolution,[],[f393,f66])).
% 1.53/0.57  % (5561)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.53/0.57  fof(f393,plain,(
% 1.53/0.57    ( ! [X5] : (~r2_hidden(X5,sK3)) )),
% 1.53/0.57    inference(resolution,[],[f314,f103])).
% 1.53/0.57  fof(f314,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.53/0.57    inference(forward_demodulation,[],[f302,f87])).
% 1.53/0.57  fof(f302,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.53/0.57    inference(superposition,[],[f54,f298])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (5573)------------------------------
% 1.53/0.57  % (5573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (5573)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (5573)Memory used [KB]: 6396
% 1.53/0.57  % (5573)Time elapsed: 0.133 s
% 1.53/0.57  % (5573)------------------------------
% 1.53/0.57  % (5573)------------------------------
% 1.53/0.57  % (5563)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.53/0.57  % (5551)Success in time 0.205 s
%------------------------------------------------------------------------------
