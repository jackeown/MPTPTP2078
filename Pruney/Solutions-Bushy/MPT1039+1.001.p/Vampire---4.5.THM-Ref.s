%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1039+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:08 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 (2146 expanded)
%              Number of leaves         :    3 ( 364 expanded)
%              Depth                    :   28
%              Number of atoms          :  509 (19184 expanded)
%              Number of equality atoms :   60 (3148 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f411,f258])).

fof(f258,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f237,f257])).

% (22560)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f257,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f256])).

fof(f256,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f12,f235])).

fof(f235,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f234,f170])).

fof(f170,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f169,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_2)).

fof(f169,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f89,f14])).

fof(f14,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = X3
      | m1_subset_1(sK4(X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f88,f13])).

fof(f13,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f88,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = X3
      | m1_subset_1(sK4(X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f77,f16])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = X3
      | m1_subset_1(sK4(X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f15,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_partfun1)).

fof(f15,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f234,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f233,f14])).

fof(f233,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f232,f17])).

fof(f232,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK4(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f229,f162])).

fof(f162,plain,
    ( v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f161,f17])).

fof(f161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | v1_partfun1(sK4(sK0,sK1,sK2,sK3),sK0) ),
    inference(resolution,[],[f91,f14])).

fof(f91,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X5
      | v1_partfun1(sK4(X4,X5,sK2,sK3),X4) ) ),
    inference(subsumption_resolution,[],[f90,f13])).

fof(f90,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X5
      | v1_partfun1(sK4(X4,X5,sK2,sK3),X4) ) ),
    inference(subsumption_resolution,[],[f78,f16])).

fof(f78,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X5
      | v1_partfun1(sK4(X4,X5,sK2,sK3),X4) ) ),
    inference(resolution,[],[f15,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | v1_partfun1(sK4(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK4(X0,X1,sK2,sK3),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f228,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_funct_1(sK4(X0,X1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f86,f13])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_funct_1(sK4(X0,X1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f76,f16])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_funct_1(sK4(X0,X1,sK2,sK3)) ) ),
    inference(resolution,[],[f15,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ v1_partfun1(sK4(X0,X1,sK2,sK3),sK0) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ v1_partfun1(sK4(X0,X1,sK2,sK3),sK0) ) ),
    inference(resolution,[],[f226,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK4(X0,X1,sK2,sK3),sK0,sK1)
      | ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f225,f87])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(X0,X1,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f224,f13])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(X0,X1,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f223,f15])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(X0,X1,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f222,f16])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(X0,X1,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(X0,X1,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(X0,X1,sK2,sK3))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(sK2,sK3) ) ),
    inference(resolution,[],[f124,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_partfun1(sK2,sK4(X0,X1,X2,sK3))
      | ~ m1_subset_1(sK4(X0,X1,X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(X0,X1,X2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(X0,X1,X2,sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f120,f13])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK4(X0,X1,X2,sK3),sK0,sK1)
      | ~ m1_subset_1(sK4(X0,X1,X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_partfun1(sK2,sK4(X0,X1,X2,sK3))
      | ~ v1_funct_1(sK4(X0,X1,X2,sK3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,sK3) ) ),
    inference(resolution,[],[f11,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,(
    ! [X4] :
      ( ~ r1_partfun1(sK3,X4)
      | ~ v1_funct_2(X4,sK0,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_partfun1(sK2,X4)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f237,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f14,f235])).

fof(f411,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f404,f259])).

fof(f259,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f238,f257])).

fof(f238,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f17,f235])).

fof(f404,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f271,f312])).

fof(f312,plain,(
    m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f280,f259])).

fof(f280,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f258,f95])).

% (22562)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f95,plain,(
    ! [X13] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
      | m1_subset_1(sK4(k1_xboole_0,X13,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))) ) ),
    inference(subsumption_resolution,[],[f94,f13])).

fof(f94,plain,(
    ! [X13] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
      | m1_subset_1(sK4(k1_xboole_0,X13,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))) ) ),
    inference(subsumption_resolution,[],[f84,f16])).

fof(f84,plain,(
    ! [X13] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13)))
      | m1_subset_1(sK4(k1_xboole_0,X13,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X13))) ) ),
    inference(resolution,[],[f15,f32])).

fof(f32,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | m1_subset_1(sK4(k1_xboole_0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f271,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(forward_demodulation,[],[f270,f257])).

fof(f270,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(subsumption_resolution,[],[f260,f93])).

fof(f93,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | v1_partfun1(sK4(k1_xboole_0,X12,sK2,sK3),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f92,f13])).

fof(f92,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | v1_partfun1(sK4(k1_xboole_0,X12,sK2,sK3),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f83,f16])).

fof(f83,plain,(
    ! [X12] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | v1_partfun1(sK4(k1_xboole_0,X12,sK2,sK3),k1_xboole_0) ) ),
    inference(resolution,[],[f15,f31])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | v1_partfun1(sK4(k1_xboole_0,X1,X2,X3),k1_xboole_0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | v1_partfun1(sK4(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f260,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK4(k1_xboole_0,X0,sK2,sK3),k1_xboole_0)
      | ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(backward_demodulation,[],[f245,f257])).

fof(f245,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
      | ~ v1_partfun1(sK4(k1_xboole_0,X0,sK2,sK3),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(backward_demodulation,[],[f213,f235])).

fof(f213,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK4(k1_xboole_0,X0,sK2,sK3),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f212,f97])).

fof(f97,plain,(
    ! [X14] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
      | v1_funct_1(sK4(k1_xboole_0,X14,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f96,f13])).

fof(f96,plain,(
    ! [X14] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
      | v1_funct_1(sK4(k1_xboole_0,X14,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f85,f16])).

fof(f85,plain,(
    ! [X14] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X14)))
      | v1_funct_1(sK4(k1_xboole_0,X14,sK2,sK3)) ) ),
    inference(resolution,[],[f15,f33])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ v1_partfun1(sK4(k1_xboole_0,X0,sK2,sK3),sK0) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ v1_partfun1(sK4(k1_xboole_0,X0,sK2,sK3),sK0) ) ),
    inference(resolution,[],[f194,f18])).

fof(f194,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4(k1_xboole_0,X0,sK2,sK3),sK0,sK1)
      | ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(subsumption_resolution,[],[f193,f97])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(k1_xboole_0,X0,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(subsumption_resolution,[],[f192,f13])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(k1_xboole_0,X0,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f191,f15])).

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(k1_xboole_0,X0,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f190,f16])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(k1_xboole_0,X0,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(k1_xboole_0,X0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(k1_xboole_0,X0,sK2,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(k1_xboole_0,X0,sK2,sK3))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_partfun1(sK2,sK3) ) ),
    inference(resolution,[],[f126,f30])).

fof(f30,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X2,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f126,plain,(
    ! [X6,X7] :
      ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,X6,X7,sK3))
      | ~ m1_subset_1(sK4(k1_xboole_0,X6,X7,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK4(k1_xboole_0,X6,X7,sK3),sK0,sK1)
      | ~ v1_funct_1(sK4(k1_xboole_0,X6,X7,sK3))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
      | ~ r1_partfun1(X7,sK3) ) ),
    inference(subsumption_resolution,[],[f122,f13])).

fof(f122,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(sK4(k1_xboole_0,X6,X7,sK3),sK0,sK1)
      | ~ m1_subset_1(sK4(k1_xboole_0,X6,X7,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_partfun1(sK2,sK4(k1_xboole_0,X6,X7,sK3))
      | ~ v1_funct_1(sK4(k1_xboole_0,X6,X7,sK3))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X6)))
      | ~ r1_partfun1(X7,sK3) ) ),
    inference(resolution,[],[f11,f29])).

fof(f29,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(k1_xboole_0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | r1_partfun1(X3,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
