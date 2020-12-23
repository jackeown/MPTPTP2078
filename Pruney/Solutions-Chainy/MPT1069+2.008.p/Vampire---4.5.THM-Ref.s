%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:43 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 377 expanded)
%              Number of leaves         :   14 (  70 expanded)
%              Depth                    :   28
%              Number of atoms          :  429 (2412 expanded)
%              Number of equality atoms :   92 ( 481 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1144,f191])).

fof(f191,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f190,f76])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f190,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f185,f124])).

fof(f124,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f185,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f183,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f183,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f182,f68])).

fof(f68,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f182,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f181,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f181,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f149,f74])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f148,f72])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f148,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f141,f75])).

fof(f75,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f73,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f73,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1144,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1049,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1049,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f74,f1033])).

fof(f1033,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f999,f439])).

fof(f439,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f438,f191])).

fof(f438,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f398,f123])).

fof(f398,plain,(
    ! [X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) ) ),
    inference(subsumption_resolution,[],[f143,f74])).

fof(f143,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f138,f72])).

fof(f138,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
      | k1_xboole_0 = sK2
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(resolution,[],[f73,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f999,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f161,f995])).

fof(f995,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f993,f71])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f993,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | k1_xboole_0 = k1_relat_1(sK4)
      | k1_xboole_0 = sK2 ) ),
    inference(condensation,[],[f990])).

fof(f990,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k1_relat_1(sK4)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) ) ),
    inference(resolution,[],[f989,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f989,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK4,sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k1_relat_1(sK4)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f987,f197])).

fof(f197,plain,(
    r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f193,f66])).

fof(f66,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f187,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f187,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f185,f74])).

fof(f987,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK4,sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(sK5,sK1)
      | k1_xboole_0 = k1_relat_1(sK4)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f986,f761])).

fof(f761,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4))
      | ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = k1_relat_1(sK4)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f714,f161])).

fof(f714,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X4)
      | k1_xboole_0 = sK2
      | ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = X4
      | r2_hidden(k1_funct_1(sK3,X5),X4) ) ),
    inference(subsumption_resolution,[],[f364,f398])).

fof(f364,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4)))
      | ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = X4
      | r2_hidden(k1_funct_1(sK3,X5),X4) ) ),
    inference(subsumption_resolution,[],[f359,f72])).

fof(f359,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X4)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4)))
      | ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = X4
      | r2_hidden(k1_funct_1(sK3,X5),X4) ) ),
    inference(resolution,[],[f356,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f356,plain,(
    ! [X0] :
      ( v1_funct_2(sK3,sK1,X0)
      | k1_xboole_0 = sK2
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) ) ),
    inference(subsumption_resolution,[],[f142,f74])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | k1_xboole_0 = sK2
      | v1_funct_2(sK3,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f137,f72])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
      | k1_xboole_0 = sK2
      | v1_funct_2(sK3,sK1,X0) ) ),
    inference(resolution,[],[f73,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f986,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
      | ~ v5_relat_1(sK4,sK0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f985,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f985,plain,
    ( ~ v1_relat_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v5_relat_1(sK4,sK0) ),
    inference(subsumption_resolution,[],[f984,f70])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f984,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f983])).

fof(f983,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f982,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f982,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f981,f71])).

fof(f981,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f980,f67])).

fof(f67,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f980,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f978,f70])).

fof(f978,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f69,f483])).

fof(f483,plain,(
    ! [X4,X5] :
      ( k1_funct_1(k8_funct_2(sK1,sK2,X5,sK3,X4),sK5) = k1_funct_1(X4,k1_funct_1(sK3,sK5))
      | ~ v1_funct_1(X4)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X5,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) ) ),
    inference(resolution,[],[f460,f66])).

fof(f460,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3))
      | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f147,f74])).

fof(f147,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3))
      | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f146,f68])).

fof(f146,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f145,f75])).

fof(f145,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f140,f72])).

fof(f140,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(sK3)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5)) ) ),
    inference(resolution,[],[f73,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f69,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f161,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f159,f71])).

fof(f159,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f67,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (12608)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.48  % (12617)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (12632)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (12615)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (12607)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (12616)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (12621)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (12604)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.57  % (12625)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.57  % (12611)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.58  % (12629)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.58  % (12603)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.58  % (12624)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.74/0.59  % (12627)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.74/0.59  % (12619)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.74/0.60  % (12610)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.74/0.60  % (12601)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.74/0.60  % (12609)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.74/0.60  % (12620)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.74/0.61  % (12602)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.74/0.61  % (12623)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.74/0.61  % (12606)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.74/0.61  % (12628)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.74/0.62  % (12613)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.74/0.62  % (12631)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.13/0.65  % (12605)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 2.22/0.65  % (12612)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.22/0.66  % (12626)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.22/0.68  % (12622)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.22/0.69  % (12630)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.65/0.71  % (12624)Refutation found. Thanks to Tanya!
% 2.65/0.71  % SZS status Theorem for theBenchmark
% 2.65/0.71  % SZS output start Proof for theBenchmark
% 2.65/0.71  fof(f1145,plain,(
% 2.65/0.71    $false),
% 2.65/0.71    inference(subsumption_resolution,[],[f1144,f191])).
% 2.65/0.71  fof(f191,plain,(
% 2.65/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.65/0.71    inference(subsumption_resolution,[],[f190,f76])).
% 2.65/0.71  fof(f76,plain,(
% 2.65/0.71    v1_xboole_0(k1_xboole_0)),
% 2.65/0.71    inference(cnf_transformation,[],[f3])).
% 2.65/0.71  fof(f3,axiom,(
% 2.65/0.71    v1_xboole_0(k1_xboole_0)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.65/0.71  fof(f190,plain,(
% 2.65/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 2.65/0.71    inference(superposition,[],[f185,f124])).
% 2.65/0.71  fof(f124,plain,(
% 2.65/0.71    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.65/0.71    inference(equality_resolution,[],[f102])).
% 2.65/0.71  fof(f102,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f7])).
% 2.65/0.71  fof(f7,axiom,(
% 2.65/0.71    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.65/0.71  fof(f185,plain,(
% 2.65/0.71    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X1)) )),
% 2.65/0.71    inference(resolution,[],[f183,f89])).
% 2.65/0.71  fof(f89,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f39])).
% 2.65/0.71  fof(f39,plain,(
% 2.65/0.71    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.65/0.71    inference(ennf_transformation,[],[f21])).
% 2.65/0.71  fof(f21,axiom,(
% 2.65/0.71    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 2.65/0.71  fof(f183,plain,(
% 2.65/0.71    ~v1_xboole_0(sK3)),
% 2.65/0.71    inference(subsumption_resolution,[],[f182,f68])).
% 2.65/0.71  fof(f68,plain,(
% 2.65/0.71    k1_xboole_0 != sK1),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f33,plain,(
% 2.65/0.71    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.65/0.71    inference(flattening,[],[f32])).
% 2.65/0.71  fof(f32,plain,(
% 2.65/0.71    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.65/0.71    inference(ennf_transformation,[],[f31])).
% 2.65/0.71  fof(f31,negated_conjecture,(
% 2.65/0.71    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.65/0.71    inference(negated_conjecture,[],[f30])).
% 2.65/0.71  fof(f30,conjecture,(
% 2.65/0.71    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 2.65/0.71  fof(f182,plain,(
% 2.65/0.71    ~v1_xboole_0(sK3) | k1_xboole_0 = sK1),
% 2.65/0.71    inference(resolution,[],[f181,f81])).
% 2.65/0.71  fof(f81,plain,(
% 2.65/0.71    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.65/0.71    inference(cnf_transformation,[],[f36])).
% 2.65/0.71  fof(f36,plain,(
% 2.65/0.71    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.65/0.71    inference(ennf_transformation,[],[f4])).
% 2.65/0.71  fof(f4,axiom,(
% 2.65/0.71    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.65/0.71  fof(f181,plain,(
% 2.65/0.71    v1_xboole_0(sK1) | ~v1_xboole_0(sK3)),
% 2.65/0.71    inference(subsumption_resolution,[],[f149,f74])).
% 2.65/0.71  fof(f74,plain,(
% 2.65/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f149,plain,(
% 2.65/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1) | ~v1_xboole_0(sK3)),
% 2.65/0.71    inference(subsumption_resolution,[],[f148,f72])).
% 2.65/0.71  fof(f72,plain,(
% 2.65/0.71    v1_funct_1(sK3)),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f148,plain,(
% 2.65/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | ~v1_xboole_0(sK3)),
% 2.65/0.71    inference(subsumption_resolution,[],[f141,f75])).
% 2.65/0.71  fof(f75,plain,(
% 2.65/0.71    ~v1_xboole_0(sK2)),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f141,plain,(
% 2.65/0.71    v1_xboole_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | ~v1_xboole_0(sK3)),
% 2.65/0.71    inference(resolution,[],[f73,f91])).
% 2.65/0.71  fof(f91,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_xboole_0(X2)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f43])).
% 2.65/0.71  fof(f43,plain,(
% 2.65/0.71    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.65/0.71    inference(flattening,[],[f42])).
% 2.65/0.71  fof(f42,plain,(
% 2.65/0.71    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.65/0.71    inference(ennf_transformation,[],[f24])).
% 2.65/0.71  fof(f24,axiom,(
% 2.65/0.71    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).
% 2.65/0.71  fof(f73,plain,(
% 2.65/0.71    v1_funct_2(sK3,sK1,sK2)),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f1144,plain,(
% 2.65/0.71    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.65/0.71    inference(forward_demodulation,[],[f1049,f123])).
% 2.65/0.71  fof(f123,plain,(
% 2.65/0.71    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.65/0.71    inference(equality_resolution,[],[f103])).
% 2.65/0.71  fof(f103,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f7])).
% 2.65/0.71  fof(f1049,plain,(
% 2.65/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.65/0.71    inference(backward_demodulation,[],[f74,f1033])).
% 2.65/0.71  fof(f1033,plain,(
% 2.65/0.71    k1_xboole_0 = sK2),
% 2.65/0.71    inference(subsumption_resolution,[],[f999,f439])).
% 2.65/0.71  fof(f439,plain,(
% 2.65/0.71    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | k1_xboole_0 = sK2),
% 2.65/0.71    inference(subsumption_resolution,[],[f438,f191])).
% 2.65/0.71  fof(f438,plain,(
% 2.65/0.71    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)),
% 2.65/0.71    inference(superposition,[],[f398,f123])).
% 2.65/0.71  fof(f398,plain,(
% 2.65/0.71    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f143,f74])).
% 2.65/0.71  fof(f143,plain,(
% 2.65/0.71    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f138,f72])).
% 2.65/0.71  fof(f138,plain,(
% 2.65/0.71    ( ! [X1] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 2.65/0.71    inference(resolution,[],[f73,f120])).
% 2.65/0.71  fof(f120,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.65/0.71    inference(cnf_transformation,[],[f65])).
% 2.65/0.71  fof(f65,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.65/0.71    inference(flattening,[],[f64])).
% 2.65/0.71  fof(f64,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.65/0.71    inference(ennf_transformation,[],[f29])).
% 2.65/0.71  fof(f29,axiom,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 2.65/0.71  fof(f999,plain,(
% 2.65/0.71    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | k1_xboole_0 = sK2),
% 2.65/0.71    inference(superposition,[],[f161,f995])).
% 2.65/0.71  fof(f995,plain,(
% 2.65/0.71    k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 2.65/0.71    inference(resolution,[],[f993,f71])).
% 2.65/0.71  fof(f71,plain,(
% 2.65/0.71    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f993,plain,(
% 2.65/0.71    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2) )),
% 2.65/0.71    inference(condensation,[],[f990])).
% 2.65/0.71  fof(f990,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))) )),
% 2.65/0.71    inference(resolution,[],[f989,f110])).
% 2.65/0.71  fof(f110,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.71    inference(cnf_transformation,[],[f57])).
% 2.65/0.71  fof(f57,plain,(
% 2.65/0.71    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.71    inference(ennf_transformation,[],[f20])).
% 2.65/0.71  fof(f20,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.65/0.71  fof(f989,plain,(
% 2.65/0.71    ( ! [X0,X1] : (~v5_relat_1(sK4,sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f987,f197])).
% 2.65/0.71  fof(f197,plain,(
% 2.65/0.71    r2_hidden(sK5,sK1)),
% 2.65/0.71    inference(resolution,[],[f193,f66])).
% 2.65/0.71  fof(f66,plain,(
% 2.65/0.71    m1_subset_1(sK5,sK1)),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f193,plain,(
% 2.65/0.71    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(X0,sK1)) )),
% 2.65/0.71    inference(resolution,[],[f187,f90])).
% 2.65/0.71  fof(f90,plain,(
% 2.65/0.71    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f41])).
% 2.65/0.71  fof(f41,plain,(
% 2.65/0.71    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.65/0.71    inference(flattening,[],[f40])).
% 2.65/0.71  fof(f40,plain,(
% 2.65/0.71    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.65/0.71    inference(ennf_transformation,[],[f10])).
% 2.65/0.71  fof(f10,axiom,(
% 2.65/0.71    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.65/0.71  fof(f187,plain,(
% 2.65/0.71    ~v1_xboole_0(sK1)),
% 2.65/0.71    inference(resolution,[],[f185,f74])).
% 2.65/0.71  fof(f987,plain,(
% 2.65/0.71    ( ! [X0,X1] : (~v5_relat_1(sK4,sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(sK5,sK1) | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2) )),
% 2.65/0.71    inference(resolution,[],[f986,f761])).
% 2.65/0.71  fof(f761,plain,(
% 2.65/0.71    ( ! [X1] : (r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) | ~r2_hidden(X1,sK1) | k1_xboole_0 = k1_relat_1(sK4) | k1_xboole_0 = sK2) )),
% 2.65/0.71    inference(resolution,[],[f714,f161])).
% 2.65/0.71  fof(f714,plain,(
% 2.65/0.71    ( ! [X4,X5] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X4) | k1_xboole_0 = sK2 | ~r2_hidden(X5,sK1) | k1_xboole_0 = X4 | r2_hidden(k1_funct_1(sK3,X5),X4)) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f364,f398])).
% 2.65/0.71  fof(f364,plain,(
% 2.65/0.71    ( ! [X4,X5] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))) | ~r2_hidden(X5,sK1) | k1_xboole_0 = X4 | r2_hidden(k1_funct_1(sK3,X5),X4)) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f359,f72])).
% 2.65/0.71  fof(f359,plain,(
% 2.65/0.71    ( ! [X4,X5] : (k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X4) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))) | ~r2_hidden(X5,sK1) | k1_xboole_0 = X4 | r2_hidden(k1_funct_1(sK3,X5),X4)) )),
% 2.65/0.71    inference(resolution,[],[f356,f116])).
% 2.65/0.71  fof(f116,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f63])).
% 2.65/0.71  fof(f63,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.65/0.71    inference(flattening,[],[f62])).
% 2.65/0.71  fof(f62,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.65/0.71    inference(ennf_transformation,[],[f28])).
% 2.65/0.71  fof(f28,axiom,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 2.65/0.71  fof(f356,plain,(
% 2.65/0.71    ( ! [X0] : (v1_funct_2(sK3,sK1,X0) | k1_xboole_0 = sK2 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f142,f74])).
% 2.65/0.71  fof(f142,plain,(
% 2.65/0.71    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X0)) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f137,f72])).
% 2.65/0.71  fof(f137,plain,(
% 2.65/0.71    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X0)) )),
% 2.65/0.71    inference(resolution,[],[f73,f119])).
% 2.65/0.71  fof(f119,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f65])).
% 2.65/0.71  fof(f986,plain,(
% 2.65/0.71    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.71    inference(resolution,[],[f985,f106])).
% 2.65/0.71  fof(f106,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.71    inference(cnf_transformation,[],[f54])).
% 2.65/0.71  fof(f54,plain,(
% 2.65/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.71    inference(ennf_transformation,[],[f19])).
% 2.65/0.71  fof(f19,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.65/0.71  fof(f985,plain,(
% 2.65/0.71    ~v1_relat_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK0)),
% 2.65/0.71    inference(subsumption_resolution,[],[f984,f70])).
% 2.65/0.71  fof(f70,plain,(
% 2.65/0.71    v1_funct_1(sK4)),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f984,plain,(
% 2.65/0.71    ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 2.65/0.71    inference(trivial_inequality_removal,[],[f983])).
% 2.65/0.71  fof(f983,plain,(
% 2.65/0.71    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 2.65/0.71    inference(superposition,[],[f982,f93])).
% 2.65/0.71  fof(f93,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f47])).
% 2.65/0.71  fof(f47,plain,(
% 2.65/0.71    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.65/0.71    inference(flattening,[],[f46])).
% 2.65/0.71  fof(f46,plain,(
% 2.65/0.71    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.65/0.71    inference(ennf_transformation,[],[f25])).
% 2.65/0.71  fof(f25,axiom,(
% 2.65/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 2.65/0.71  fof(f982,plain,(
% 2.65/0.71    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 2.65/0.71    inference(subsumption_resolution,[],[f981,f71])).
% 2.65/0.71  fof(f981,plain,(
% 2.65/0.71    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.65/0.71    inference(subsumption_resolution,[],[f980,f67])).
% 2.65/0.71  fof(f67,plain,(
% 2.65/0.71    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f980,plain,(
% 2.65/0.71    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.65/0.71    inference(subsumption_resolution,[],[f978,f70])).
% 2.65/0.71  fof(f978,plain,(
% 2.65/0.71    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.65/0.71    inference(superposition,[],[f69,f483])).
% 2.65/0.71  fof(f483,plain,(
% 2.65/0.71    ( ! [X4,X5] : (k1_funct_1(k8_funct_2(sK1,sK2,X5,sK3,X4),sK5) = k1_funct_1(X4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(X4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X5,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X5)))) )),
% 2.65/0.71    inference(resolution,[],[f460,f66])).
% 2.65/0.71  fof(f460,plain,(
% 2.65/0.71    ( ! [X4,X5,X3] : (~m1_subset_1(X5,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3)) | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5))) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f147,f74])).
% 2.65/0.71  fof(f147,plain,(
% 2.65/0.71    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~m1_subset_1(X5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3)) | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5))) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f146,f68])).
% 2.65/0.71  fof(f146,plain,(
% 2.65/0.71    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~m1_subset_1(X5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5))) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f145,f75])).
% 2.65/0.71  fof(f145,plain,(
% 2.65/0.71    ( ! [X4,X5,X3] : (v1_xboole_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~m1_subset_1(X5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5))) )),
% 2.65/0.71    inference(subsumption_resolution,[],[f140,f72])).
% 2.65/0.71  fof(f140,plain,(
% 2.65/0.71    ( ! [X4,X5,X3] : (~v1_funct_1(sK3) | v1_xboole_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~m1_subset_1(X5,sK1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X4,X3)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,X4,sK3,X3),X5) = k1_funct_1(X3,k1_funct_1(sK3,X5))) )),
% 2.65/0.71    inference(resolution,[],[f73,f105])).
% 2.65/0.71  fof(f105,plain,(
% 2.65/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 2.65/0.71    inference(cnf_transformation,[],[f53])).
% 2.65/0.71  fof(f53,plain,(
% 2.65/0.71    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.65/0.71    inference(flattening,[],[f52])).
% 2.65/0.71  fof(f52,plain,(
% 2.65/0.71    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.65/0.71    inference(ennf_transformation,[],[f26])).
% 2.65/0.71  fof(f26,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 2.65/0.71  fof(f69,plain,(
% 2.65/0.71    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f161,plain,(
% 2.65/0.71    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 2.65/0.71    inference(subsumption_resolution,[],[f159,f71])).
% 2.65/0.71  fof(f159,plain,(
% 2.65/0.71    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.65/0.71    inference(superposition,[],[f67,f107])).
% 2.65/0.71  fof(f107,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.71    inference(cnf_transformation,[],[f55])).
% 2.65/0.71  fof(f55,plain,(
% 2.65/0.71    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.71    inference(ennf_transformation,[],[f22])).
% 2.65/0.71  fof(f22,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.65/0.71  % SZS output end Proof for theBenchmark
% 2.65/0.71  % (12624)------------------------------
% 2.65/0.71  % (12624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.65/0.71  % (12624)Termination reason: Refutation
% 2.65/0.71  
% 2.65/0.71  % (12624)Memory used [KB]: 2174
% 2.65/0.71  % (12624)Time elapsed: 0.290 s
% 2.65/0.71  % (12624)------------------------------
% 2.65/0.71  % (12624)------------------------------
% 2.65/0.74  % (12592)Success in time 0.376 s
%------------------------------------------------------------------------------
