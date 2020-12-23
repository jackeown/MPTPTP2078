%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 266 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   21
%              Number of atoms          :  345 (1544 expanded)
%              Number of equality atoms :   85 ( 329 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(subsumption_resolution,[],[f254,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f254,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f250])).

fof(f250,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f249,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f249,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f243,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f243,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f240,f190])).

fof(f190,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f39,f189])).

fof(f189,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f188,f41])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f188,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f187,f40])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f187,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f186,f91])).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f85,f88])).

fof(f88,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f59,f41])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f85,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(backward_demodulation,[],[f37,f84])).

fof(f84,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f186,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[],[f141,f88])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f140,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f134,f43])).

fof(f43,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(superposition,[],[f103,f84])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) ) ),
    inference(subsumption_resolution,[],[f100,f38])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | v1_xboole_0(X1)
      | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) ) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f39,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f240,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK1)
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f214,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f107,f40])).

% (2706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f107,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f104,f76])).

fof(f76,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f74,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f81,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(resolution,[],[f60,f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f214,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f177,f78])).

fof(f78,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f177,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f126,f129])).

fof(f129,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f99,f89])).

fof(f89,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f59,f44])).

fof(f99,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f97,f43])).

% (2689)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (2700)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (2706)Refutation not found, incomplete strategy% (2706)------------------------------
% (2706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2706)Termination reason: Refutation not found, incomplete strategy

% (2706)Memory used [KB]: 10618
% (2706)Time elapsed: 0.097 s
% (2706)------------------------------
% (2706)------------------------------
% (2685)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (2704)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (2698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (2698)Refutation not found, incomplete strategy% (2698)------------------------------
% (2698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2698)Termination reason: Refutation not found, incomplete strategy

% (2698)Memory used [KB]: 6140
% (2698)Time elapsed: 0.099 s
% (2698)------------------------------
% (2698)------------------------------
% (2705)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (2701)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (2692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f97,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(resolution,[],[f66,f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f126,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f121,f77])).

fof(f77,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f75,f51])).

fof(f75,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f47,f44])).

fof(f121,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f90,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f90,plain,(
    v5_relat_1(sK3,k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f87,f88])).

fof(f87,plain,(
    v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) ),
    inference(subsumption_resolution,[],[f86,f77])).

fof(f86,plain,
    ( ~ v1_relat_1(sK3)
    | v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) ),
    inference(resolution,[],[f85,f52])).

% (2696)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f45,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (2691)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (2699)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (2697)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (2694)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (2695)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (2697)Refutation not found, incomplete strategy% (2697)------------------------------
% 0.22/0.50  % (2697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2697)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (2697)Memory used [KB]: 10746
% 0.22/0.50  % (2697)Time elapsed: 0.044 s
% 0.22/0.50  % (2697)------------------------------
% 0.22/0.50  % (2697)------------------------------
% 0.22/0.51  % (2693)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (2690)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (2703)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (2686)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (2687)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (2686)Refutation not found, incomplete strategy% (2686)------------------------------
% 0.22/0.51  % (2686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2686)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (2686)Memory used [KB]: 10618
% 0.22/0.51  % (2686)Time elapsed: 0.053 s
% 0.22/0.51  % (2686)------------------------------
% 0.22/0.51  % (2686)------------------------------
% 0.22/0.51  % (2703)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f254,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f45,f250])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    k1_xboole_0 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f249,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    k1_xboole_0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f243,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(resolution,[],[f50,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f240,f190])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(backward_demodulation,[],[f39,f189])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(subsumption_resolution,[],[f187,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(subsumption_resolution,[],[f186,f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.22/0.51    inference(backward_demodulation,[],[f85,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.22/0.51    inference(resolution,[],[f59,f41])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    inference(backward_demodulation,[],[f37,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.51    inference(resolution,[],[f58,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(superposition,[],[f141,f88])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f139,f45])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f44])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.22/0.51    inference(superposition,[],[f103,f84])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f38])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) )),
% 0.22/0.51    inference(resolution,[],[f57,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    m1_subset_1(sK5,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | v1_xboole_0(sK1) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(resolution,[],[f214,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f40])).
% 0.22/0.51  % (2706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    v1_relat_1(sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK4)),
% 0.22/0.51    inference(resolution,[],[f47,f41])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.22/0.51    inference(resolution,[],[f81,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    v5_relat_1(sK4,sK0)),
% 0.22/0.51    inference(resolution,[],[f60,f41])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f177,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f54,f36])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | k1_xboole_0 = sK2) )),
% 0.22/0.51    inference(superposition,[],[f126,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(superposition,[],[f99,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.22/0.51    inference(resolution,[],[f59,f44])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f43])).
% 0.22/0.51  % (2689)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (2700)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (2706)Refutation not found, incomplete strategy% (2706)------------------------------
% 0.22/0.52  % (2706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2706)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2706)Memory used [KB]: 10618
% 0.22/0.52  % (2706)Time elapsed: 0.097 s
% 0.22/0.52  % (2706)------------------------------
% 0.22/0.52  % (2706)------------------------------
% 0.22/0.52  % (2685)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (2704)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (2698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (2698)Refutation not found, incomplete strategy% (2698)------------------------------
% 0.22/0.52  % (2698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2698)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2698)Memory used [KB]: 6140
% 0.22/0.52  % (2698)Time elapsed: 0.099 s
% 0.22/0.52  % (2698)------------------------------
% 0.22/0.52  % (2698)------------------------------
% 0.22/0.52  % (2705)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (2701)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.23/0.52  % (2692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.23/0.53  fof(f97,plain,(
% 1.23/0.53    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2)),
% 1.23/0.53    inference(resolution,[],[f66,f44])).
% 1.23/0.53  fof(f66,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f35])).
% 1.23/0.53  fof(f35,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(flattening,[],[f34])).
% 1.23/0.53  fof(f34,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(ennf_transformation,[],[f12])).
% 1.23/0.53  fof(f12,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.23/0.53  fof(f126,plain,(
% 1.23/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4))) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f125,f42])).
% 1.23/0.53  fof(f125,plain,(
% 1.23/0.53    ( ! [X1] : (~v1_funct_1(sK3) | ~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4))) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f121,f77])).
% 1.23/0.53  fof(f77,plain,(
% 1.23/0.53    v1_relat_1(sK3)),
% 1.23/0.53    inference(subsumption_resolution,[],[f75,f51])).
% 1.23/0.53  fof(f75,plain,(
% 1.23/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3)),
% 1.23/0.53    inference(resolution,[],[f47,f44])).
% 1.23/0.53  fof(f121,plain,(
% 1.23/0.53    ( ! [X1] : (~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X1),k1_relat_1(sK4))) )),
% 1.23/0.53    inference(resolution,[],[f90,f55])).
% 1.23/0.53  fof(f55,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f26])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(flattening,[],[f25])).
% 1.23/0.53  fof(f25,plain,(
% 1.23/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.23/0.53    inference(ennf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,axiom,(
% 1.23/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.23/0.53  fof(f90,plain,(
% 1.23/0.53    v5_relat_1(sK3,k1_relat_1(sK4))),
% 1.23/0.53    inference(backward_demodulation,[],[f87,f88])).
% 1.23/0.53  fof(f87,plain,(
% 1.23/0.53    v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))),
% 1.23/0.53    inference(subsumption_resolution,[],[f86,f77])).
% 1.23/0.53  fof(f86,plain,(
% 1.23/0.53    ~v1_relat_1(sK3) | v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))),
% 1.23/0.53    inference(resolution,[],[f85,f52])).
% 1.23/0.53  % (2696)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.23/0.53  fof(f52,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f22])).
% 1.23/0.53  fof(f22,plain,(
% 1.23/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(ennf_transformation,[],[f6])).
% 1.23/0.53  fof(f6,axiom,(
% 1.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.23/0.53  fof(f45,plain,(
% 1.23/0.53    ~v1_xboole_0(sK2)),
% 1.23/0.53    inference(cnf_transformation,[],[f19])).
% 1.23/0.53  % SZS output end Proof for theBenchmark
% 1.23/0.53  % (2703)------------------------------
% 1.23/0.53  % (2703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (2703)Termination reason: Refutation
% 1.23/0.53  
% 1.23/0.53  % (2703)Memory used [KB]: 1918
% 1.23/0.53  % (2703)Time elapsed: 0.089 s
% 1.23/0.53  % (2703)------------------------------
% 1.23/0.53  % (2703)------------------------------
% 1.23/0.53  % (2683)Success in time 0.156 s
%------------------------------------------------------------------------------
