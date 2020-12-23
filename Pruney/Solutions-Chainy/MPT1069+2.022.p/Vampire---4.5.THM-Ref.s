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
% DateTime   : Thu Dec  3 13:07:45 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  120 (1931 expanded)
%              Number of leaves         :   17 ( 358 expanded)
%              Depth                    :   39
%              Number of atoms          :  369 (11824 expanded)
%              Number of equality atoms :   95 (2621 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(subsumption_resolution,[],[f435,f238])).

fof(f238,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f234])).

fof(f234,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f233,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f233,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f229,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f229,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f228,f98])).

fof(f98,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f45,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f228,plain,
    ( ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f226,f193])).

fof(f193,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f192,f110])).

fof(f110,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f192,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f99,f53])).

fof(f99,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f52,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f226,plain,(
    ~ r2_hidden(sK5,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f225,f112])).

fof(f112,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f225,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f224,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f224,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f222,f146])).

fof(f146,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f130,f111])).

fof(f111,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f53,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f130,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f46,f100])).

fof(f100,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f50,f78])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f222,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f220,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f220,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5),X0)
      | ~ r1_tarski(X0,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f219,f50])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r2_hidden(k1_funct_1(sK3,sK5),X1)
      | ~ r1_tarski(X1,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f218,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f218,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f213,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f213,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v5_relat_1(sK4,sK0) ),
    inference(superposition,[],[f210,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1)
      | ~ r2_hidden(X1,k1_relat_1(sK4))
      | ~ v5_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f94,f102])).

fof(f102,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f50,f76])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK4,X0)
      | ~ v1_relat_1(sK4)
      | ~ r2_hidden(X1,k1_relat_1(sK4))
      | k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1) ) ),
    inference(resolution,[],[f49,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

% (15249)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (15245)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (15231)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (15238)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (15221)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f210,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f48,f209])).

fof(f209,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f124,f45])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f123,f47])).

% (15248)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f120,f49])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f51])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(resolution,[],[f46,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f48,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f435,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f423,f434])).

fof(f434,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f423,f56])).

fof(f423,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f419,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f419,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f404,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f404,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f403,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f403,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
      | r1_tarski(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(forward_demodulation,[],[f378,f370])).

fof(f370,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f276,f237])).

fof(f237,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f53,f234])).

fof(f276,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f274,f47])).

% (15222)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f274,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(resolution,[],[f236,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f236,plain,(
    v1_funct_2(sK3,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f234])).

fof(f378,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ) ),
    inference(backward_demodulation,[],[f174,f370])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
      | r1_tarski(k1_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f160,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f160,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f126,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f126,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK3,X1)
      | r1_tarski(k1_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f112,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (15223)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15235)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (15225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15233)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (15240)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.90/0.61  % (15244)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.90/0.61  % (15236)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.90/0.61  % (15226)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.90/0.62  % (15228)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.90/0.62  % (15232)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.90/0.62  % (15246)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.90/0.62  % (15223)Refutation not found, incomplete strategy% (15223)------------------------------
% 1.90/0.62  % (15223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (15223)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.62  
% 1.90/0.62  % (15223)Memory used [KB]: 11897
% 1.90/0.62  % (15223)Time elapsed: 0.178 s
% 1.90/0.62  % (15223)------------------------------
% 1.90/0.62  % (15223)------------------------------
% 1.90/0.62  % (15229)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.90/0.63  % (15227)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.90/0.63  % (15224)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.90/0.63  % (15239)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.90/0.63  % (15244)Refutation found. Thanks to Tanya!
% 1.90/0.63  % SZS status Theorem for theBenchmark
% 1.90/0.63  % SZS output start Proof for theBenchmark
% 1.90/0.63  fof(f440,plain,(
% 1.90/0.63    $false),
% 1.90/0.63    inference(subsumption_resolution,[],[f435,f238])).
% 1.90/0.63  fof(f238,plain,(
% 1.90/0.63    ~v1_xboole_0(k1_xboole_0)),
% 1.90/0.63    inference(backward_demodulation,[],[f54,f234])).
% 1.90/0.63  fof(f234,plain,(
% 1.90/0.63    k1_xboole_0 = sK2),
% 1.90/0.63    inference(subsumption_resolution,[],[f233,f47])).
% 1.90/0.63  fof(f47,plain,(
% 1.90/0.63    k1_xboole_0 != sK1),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f23,plain,(
% 1.90/0.63    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.90/0.63    inference(flattening,[],[f22])).
% 1.90/0.63  fof(f22,plain,(
% 1.90/0.63    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.90/0.63    inference(ennf_transformation,[],[f21])).
% 1.90/0.63  fof(f21,negated_conjecture,(
% 1.90/0.63    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.90/0.63    inference(negated_conjecture,[],[f20])).
% 1.90/0.63  fof(f20,conjecture,(
% 1.90/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 1.90/0.63  fof(f233,plain,(
% 1.90/0.63    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.90/0.63    inference(resolution,[],[f229,f56])).
% 1.90/0.63  fof(f56,plain,(
% 1.90/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.90/0.63    inference(cnf_transformation,[],[f24])).
% 1.90/0.63  fof(f24,plain,(
% 1.90/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.90/0.63    inference(ennf_transformation,[],[f3])).
% 1.90/0.63  fof(f3,axiom,(
% 1.90/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.90/0.63  fof(f229,plain,(
% 1.90/0.63    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 1.90/0.63    inference(resolution,[],[f228,f98])).
% 1.90/0.63  fof(f98,plain,(
% 1.90/0.63    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 1.90/0.63    inference(resolution,[],[f45,f62])).
% 1.90/0.63  fof(f62,plain,(
% 1.90/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f28])).
% 1.90/0.63  fof(f28,plain,(
% 1.90/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.90/0.63    inference(flattening,[],[f27])).
% 1.90/0.63  fof(f27,plain,(
% 1.90/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.90/0.63    inference(ennf_transformation,[],[f6])).
% 1.90/0.63  fof(f6,axiom,(
% 1.90/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.90/0.63  fof(f45,plain,(
% 1.90/0.63    m1_subset_1(sK5,sK1)),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f228,plain,(
% 1.90/0.63    ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK2),
% 1.90/0.63    inference(superposition,[],[f226,f193])).
% 1.90/0.63  fof(f193,plain,(
% 1.90/0.63    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.90/0.63    inference(superposition,[],[f192,f110])).
% 1.90/0.63  fof(f110,plain,(
% 1.90/0.63    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.90/0.63    inference(resolution,[],[f53,f78])).
% 1.90/0.63  fof(f78,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f41])).
% 1.90/0.63  fof(f41,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(ennf_transformation,[],[f14])).
% 1.90/0.63  fof(f14,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.90/0.63  fof(f53,plain,(
% 1.90/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f192,plain,(
% 1.90/0.63    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.90/0.63    inference(subsumption_resolution,[],[f99,f53])).
% 1.90/0.63  fof(f99,plain,(
% 1.90/0.63    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.90/0.63    inference(resolution,[],[f52,f86])).
% 1.90/0.63  fof(f86,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f44])).
% 1.90/0.63  fof(f44,plain,(
% 1.90/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(flattening,[],[f43])).
% 1.90/0.63  fof(f43,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(ennf_transformation,[],[f17])).
% 1.90/0.63  fof(f17,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.90/0.63  fof(f52,plain,(
% 1.90/0.63    v1_funct_2(sK3,sK1,sK2)),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f226,plain,(
% 1.90/0.63    ~r2_hidden(sK5,k1_relat_1(sK3))),
% 1.90/0.63    inference(subsumption_resolution,[],[f225,f112])).
% 1.90/0.63  fof(f112,plain,(
% 1.90/0.63    v1_relat_1(sK3)),
% 1.90/0.63    inference(resolution,[],[f53,f76])).
% 1.90/0.63  fof(f76,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f39])).
% 1.90/0.63  fof(f39,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(ennf_transformation,[],[f11])).
% 1.90/0.63  fof(f11,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.90/0.63  fof(f225,plain,(
% 1.90/0.63    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.90/0.63    inference(subsumption_resolution,[],[f224,f51])).
% 1.90/0.63  fof(f51,plain,(
% 1.90/0.63    v1_funct_1(sK3)),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f224,plain,(
% 1.90/0.63    ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.90/0.63    inference(subsumption_resolution,[],[f222,f146])).
% 1.90/0.63  fof(f146,plain,(
% 1.90/0.63    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 1.90/0.63    inference(backward_demodulation,[],[f130,f111])).
% 1.90/0.63  fof(f111,plain,(
% 1.90/0.63    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.90/0.63    inference(resolution,[],[f53,f77])).
% 1.90/0.63  fof(f77,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f40])).
% 1.90/0.63  fof(f40,plain,(
% 1.90/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(ennf_transformation,[],[f15])).
% 1.90/0.63  fof(f15,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.90/0.63  fof(f130,plain,(
% 1.90/0.63    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 1.90/0.63    inference(backward_demodulation,[],[f46,f100])).
% 1.90/0.63  fof(f100,plain,(
% 1.90/0.63    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 1.90/0.63    inference(resolution,[],[f50,f78])).
% 1.90/0.63  fof(f50,plain,(
% 1.90/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f46,plain,(
% 1.90/0.63    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.90/0.63    inference(cnf_transformation,[],[f23])).
% 1.90/0.63  fof(f222,plain,(
% 1.90/0.63    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.90/0.63    inference(resolution,[],[f220,f64])).
% 1.90/0.63  fof(f64,plain,(
% 1.90/0.63    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f32])).
% 1.90/0.63  fof(f32,plain,(
% 1.90/0.63    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.90/0.63    inference(flattening,[],[f31])).
% 1.90/0.63  fof(f31,plain,(
% 1.90/0.63    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.90/0.63    inference(ennf_transformation,[],[f9])).
% 1.90/0.63  fof(f9,axiom,(
% 1.90/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.90/0.63  fof(f220,plain,(
% 1.90/0.63    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),X0) | ~r1_tarski(X0,k1_relat_1(sK4))) )),
% 1.90/0.63    inference(resolution,[],[f219,f50])).
% 1.90/0.63  fof(f219,plain,(
% 1.90/0.63    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r2_hidden(k1_funct_1(sK3,sK5),X1) | ~r1_tarski(X1,k1_relat_1(sK4))) )),
% 1.90/0.63    inference(resolution,[],[f218,f69])).
% 1.90/0.63  fof(f69,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f35])).
% 1.90/0.63  fof(f35,plain,(
% 1.90/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.90/0.63    inference(ennf_transformation,[],[f2])).
% 1.90/0.63  fof(f2,axiom,(
% 1.90/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.90/0.63  fof(f218,plain,(
% 1.90/0.63    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 1.90/0.63    inference(resolution,[],[f213,f80])).
% 1.90/0.63  fof(f80,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.63    inference(cnf_transformation,[],[f42])).
% 1.90/0.63  fof(f42,plain,(
% 1.90/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.63    inference(ennf_transformation,[],[f12])).
% 1.90/0.63  fof(f12,axiom,(
% 1.90/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.90/0.63  fof(f213,plain,(
% 1.90/0.63    ~v5_relat_1(sK4,sK0) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 1.90/0.63    inference(trivial_inequality_removal,[],[f212])).
% 1.90/0.63  fof(f212,plain,(
% 1.90/0.63    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK0)),
% 1.90/0.63    inference(superposition,[],[f210,f207])).
% 1.90/0.63  fof(f207,plain,(
% 1.90/0.63    ( ! [X0,X1] : (k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1) | ~r2_hidden(X1,k1_relat_1(sK4)) | ~v5_relat_1(sK4,X0)) )),
% 1.90/0.63    inference(subsumption_resolution,[],[f94,f102])).
% 1.90/0.63  fof(f102,plain,(
% 1.90/0.63    v1_relat_1(sK4)),
% 1.90/0.63    inference(resolution,[],[f50,f76])).
% 1.90/0.63  fof(f94,plain,(
% 1.90/0.63    ( ! [X0,X1] : (~v5_relat_1(sK4,X0) | ~v1_relat_1(sK4) | ~r2_hidden(X1,k1_relat_1(sK4)) | k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1)) )),
% 1.90/0.63    inference(resolution,[],[f49,f65])).
% 1.90/0.63  fof(f65,plain,(
% 1.90/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 1.90/0.63    inference(cnf_transformation,[],[f34])).
% 1.90/0.63  fof(f34,plain,(
% 1.90/0.63    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.90/0.63    inference(flattening,[],[f33])).
% 1.90/0.63  fof(f33,plain,(
% 1.90/0.63    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.90/0.63    inference(ennf_transformation,[],[f18])).
% 1.90/0.63  fof(f18,axiom,(
% 1.90/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.90/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.90/0.64  % (15249)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.90/0.64  % (15245)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.90/0.64  % (15231)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.90/0.64  % (15238)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.90/0.65  % (15221)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.23/0.65  fof(f49,plain,(
% 2.23/0.65    v1_funct_1(sK4)),
% 2.23/0.65    inference(cnf_transformation,[],[f23])).
% 2.23/0.65  fof(f210,plain,(
% 2.23/0.65    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 2.23/0.65    inference(backward_demodulation,[],[f48,f209])).
% 2.23/0.65  fof(f209,plain,(
% 2.23/0.65    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 2.23/0.65    inference(resolution,[],[f124,f45])).
% 2.23/0.65  fof(f124,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f123,f47])).
% 2.23/0.65  % (15248)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.23/0.65  fof(f123,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f122,f54])).
% 2.23/0.65  fof(f122,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f121,f50])).
% 2.23/0.65  fof(f121,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f120,f49])).
% 2.23/0.65  fof(f120,plain,(
% 2.23/0.65    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f119,f53])).
% 2.23/0.65  fof(f119,plain,(
% 2.23/0.65    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f118,f52])).
% 2.23/0.65  fof(f118,plain,(
% 2.23/0.65    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(subsumption_resolution,[],[f115,f51])).
% 2.23/0.65  fof(f115,plain,(
% 2.23/0.65    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 2.23/0.65    inference(resolution,[],[f46,f75])).
% 2.23/0.65  fof(f75,plain,(
% 2.23/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 2.23/0.65    inference(cnf_transformation,[],[f38])).
% 2.23/0.65  fof(f38,plain,(
% 2.23/0.65    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.23/0.65    inference(flattening,[],[f37])).
% 2.23/0.65  fof(f37,plain,(
% 2.23/0.65    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.23/0.65    inference(ennf_transformation,[],[f19])).
% 2.23/0.65  fof(f19,axiom,(
% 2.23/0.65    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.23/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 2.23/0.65  fof(f48,plain,(
% 2.23/0.65    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 2.23/0.65    inference(cnf_transformation,[],[f23])).
% 2.23/0.65  fof(f54,plain,(
% 2.23/0.65    ~v1_xboole_0(sK2)),
% 2.23/0.65    inference(cnf_transformation,[],[f23])).
% 2.23/0.65  fof(f435,plain,(
% 2.23/0.65    v1_xboole_0(k1_xboole_0)),
% 2.23/0.65    inference(backward_demodulation,[],[f423,f434])).
% 2.23/0.65  fof(f434,plain,(
% 2.23/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.23/0.65    inference(resolution,[],[f423,f56])).
% 2.23/0.65  fof(f423,plain,(
% 2.23/0.65    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 2.23/0.65    inference(resolution,[],[f419,f57])).
% 2.23/0.65  fof(f57,plain,(
% 2.23/0.65    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 2.23/0.65    inference(cnf_transformation,[],[f1])).
% 2.23/0.66  fof(f1,axiom,(
% 2.23/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.23/0.66  fof(f419,plain,(
% 2.23/0.66    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.23/0.66    inference(resolution,[],[f404,f74])).
% 2.23/0.66  fof(f74,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f36])).
% 2.23/0.66  fof(f36,plain,(
% 2.23/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.23/0.66    inference(ennf_transformation,[],[f10])).
% 2.23/0.66  fof(f10,axiom,(
% 2.23/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.23/0.66  fof(f404,plain,(
% 2.23/0.66    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f403,f55])).
% 2.23/0.66  fof(f55,plain,(
% 2.23/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f5])).
% 2.23/0.66  fof(f5,axiom,(
% 2.23/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.23/0.66  fof(f403,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) | r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 2.23/0.66    inference(forward_demodulation,[],[f378,f370])).
% 2.23/0.66  fof(f370,plain,(
% 2.23/0.66    k1_xboole_0 = sK3),
% 2.23/0.66    inference(subsumption_resolution,[],[f276,f237])).
% 2.23/0.66  fof(f237,plain,(
% 2.23/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.23/0.66    inference(backward_demodulation,[],[f53,f234])).
% 2.23/0.66  fof(f276,plain,(
% 2.23/0.66    k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.23/0.66    inference(subsumption_resolution,[],[f274,f47])).
% 2.23/0.67  % (15222)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.23/0.67  fof(f274,plain,(
% 2.23/0.67    k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 2.23/0.67    inference(resolution,[],[f236,f91])).
% 2.23/0.67  fof(f91,plain,(
% 2.23/0.67    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.23/0.67    inference(equality_resolution,[],[f82])).
% 2.23/0.67  fof(f82,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f44])).
% 2.23/0.67  fof(f236,plain,(
% 2.23/0.67    v1_funct_2(sK3,sK1,k1_xboole_0)),
% 2.23/0.67    inference(backward_demodulation,[],[f52,f234])).
% 2.23/0.67  fof(f378,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~r1_tarski(sK3,k2_zfmisc_1(X0,X1))) )),
% 2.23/0.67    inference(backward_demodulation,[],[f174,f370])).
% 2.23/0.67  fof(f174,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(sK3,k2_zfmisc_1(X0,X1)) | r1_tarski(k1_relat_1(sK3),X0)) )),
% 2.23/0.67    inference(resolution,[],[f160,f72])).
% 2.23/0.67  fof(f72,plain,(
% 2.23/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f7])).
% 2.23/0.67  fof(f7,axiom,(
% 2.23/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.23/0.67  fof(f160,plain,(
% 2.23/0.67    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(sK3),X1)) )),
% 2.23/0.67    inference(resolution,[],[f126,f79])).
% 2.23/0.67  fof(f79,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f42])).
% 2.23/0.67  fof(f126,plain,(
% 2.23/0.67    ( ! [X1] : (~v4_relat_1(sK3,X1) | r1_tarski(k1_relat_1(sK3),X1)) )),
% 2.23/0.67    inference(resolution,[],[f112,f60])).
% 2.23/0.67  fof(f60,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f25])).
% 2.23/0.67  fof(f25,plain,(
% 2.23/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.67    inference(ennf_transformation,[],[f8])).
% 2.23/0.67  fof(f8,axiom,(
% 2.23/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.23/0.67  % SZS output end Proof for theBenchmark
% 2.23/0.67  % (15244)------------------------------
% 2.23/0.67  % (15244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.67  % (15244)Termination reason: Refutation
% 2.23/0.67  
% 2.23/0.67  % (15244)Memory used [KB]: 1918
% 2.23/0.67  % (15244)Time elapsed: 0.130 s
% 2.23/0.67  % (15244)------------------------------
% 2.23/0.67  % (15244)------------------------------
% 2.23/0.67  % (15231)Refutation not found, incomplete strategy% (15231)------------------------------
% 2.23/0.67  % (15231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.67  % (15231)Termination reason: Refutation not found, incomplete strategy
% 2.23/0.67  
% 2.23/0.67  % (15231)Memory used [KB]: 10874
% 2.23/0.67  % (15231)Time elapsed: 0.215 s
% 2.23/0.67  % (15231)------------------------------
% 2.23/0.67  % (15231)------------------------------
% 2.23/0.67  % (15214)Success in time 0.304 s
%------------------------------------------------------------------------------
