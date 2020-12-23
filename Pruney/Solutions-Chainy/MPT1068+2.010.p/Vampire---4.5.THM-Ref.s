%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 154 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  256 ( 985 expanded)
%              Number of equality atoms :   69 ( 213 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f183,f114])).

fof(f114,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f72,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f183,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f177])).

fof(f177,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f176,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f173,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

% (8723)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f173,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f171,f138])).

fof(f138,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f35,f137])).

fof(f137,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f106,f136])).

fof(f136,plain,(
    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f132,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f132,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f91,f37])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(sK1,sK2,X6,X7,sK3,X5) = k5_relat_1(sK3,X5) ) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_partfun1(sK1,sK2,X6,X7,sK3,X5) = k5_relat_1(sK3,X5) ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f106,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f105,plain,
    ( ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f104,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f103,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f102,f40])).

fof(f102,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f101,f39])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(f35,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,
    ( k1_xboole_0 = sK2
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f148,f70])).

fof(f70,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f146,f75])).

fof(f75,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2
      | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(resolution,[],[f99,f36])).

fof(f99,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = sK2
      | k1_funct_1(k5_relat_1(sK3,X4),X5) = k1_funct_1(X4,k1_funct_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = sK2
      | k1_funct_1(k5_relat_1(sK3,X4),X5) = k1_funct_1(X4,k1_funct_1(sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f94,f39])).

fof(f94,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = sK2
      | k1_funct_1(k5_relat_1(sK3,X4),X5) = k1_funct_1(X4,k1_funct_1(sK3,X5)) ) ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (8718)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (8722)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (8734)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (8730)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (8718)Refutation not found, incomplete strategy% (8718)------------------------------
% 0.22/0.49  % (8718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8718)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8718)Memory used [KB]: 10618
% 0.22/0.49  % (8718)Time elapsed: 0.069 s
% 0.22/0.49  % (8718)------------------------------
% 0.22/0.49  % (8718)------------------------------
% 0.22/0.49  % (8719)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (8726)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (8729)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (8731)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (8721)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (8735)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (8720)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (8727)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (8717)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (8734)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f183,f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f72,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f62,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f49,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f41,f177])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    k1_xboole_0 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    k1_xboole_0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f173,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  % (8723)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(superposition,[],[f35,f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(backward_demodulation,[],[f106,f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.51    inference(resolution,[],[f91,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X5) | k1_partfun1(sK1,sK2,X6,X7,sK3,X5) = k5_relat_1(sK3,X5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f87,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~v1_funct_1(sK3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_partfun1(sK1,sK2,X6,X7,sK3,X5) = k5_relat_1(sK3,X5)) )),
% 0.22/0.51    inference(resolution,[],[f58,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | k1_xboole_0 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f38])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f37])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f103,f36])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f40])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f101,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.51    inference(resolution,[],[f57,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f148,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f47,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    m1_subset_1(sK5,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    v1_relat_1(sK4)),
% 0.22/0.51    inference(resolution,[],[f54,f37])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(sK4) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 0.22/0.51    inference(resolution,[],[f99,f36])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r2_hidden(X5,sK1) | k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,X4),X5) = k1_funct_1(X4,k1_funct_1(sK3,X5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f38])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~v1_funct_1(sK3) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r2_hidden(X5,sK1) | k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,X4),X5) = k1_funct_1(X4,k1_funct_1(sK3,X5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f94,f39])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r2_hidden(X5,sK1) | k1_xboole_0 = sK2 | k1_funct_1(k5_relat_1(sK3,X4),X5) = k1_funct_1(X4,k1_funct_1(sK3,X5))) )),
% 0.22/0.51    inference(resolution,[],[f56,f40])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~v1_xboole_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (8734)------------------------------
% 0.22/0.51  % (8734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8734)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (8734)Memory used [KB]: 1791
% 0.22/0.51  % (8734)Time elapsed: 0.088 s
% 0.22/0.51  % (8734)------------------------------
% 0.22/0.51  % (8734)------------------------------
% 0.22/0.51  % (8716)Success in time 0.151 s
%------------------------------------------------------------------------------
