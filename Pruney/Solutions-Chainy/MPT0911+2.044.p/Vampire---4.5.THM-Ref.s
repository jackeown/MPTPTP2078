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
% DateTime   : Thu Dec  3 12:59:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 670 expanded)
%              Number of leaves         :    5 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  261 (4597 expanded)
%              Number of equality atoms :  199 (2940 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f72])).

fof(f72,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f18,f63])).

fof(f63,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f62,f15])).

% (17908)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f62,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f61,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(resolution,[],[f14,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f14,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,(
    sK3 = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f100,f64])).

fof(f64,plain,(
    sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) ),
    inference(backward_demodulation,[],[f60,f63])).

fof(f60,plain,(
    sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(backward_demodulation,[],[f56,f59])).

fof(f59,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f57,f17])).

fof(f57,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f14,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(backward_demodulation,[],[f40,f55])).

fof(f55,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f54,f15])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f53,f17])).

fof(f53,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f35,f16])).

fof(f35,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f14,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f39,f15])).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f38,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f30,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f14,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f100,plain,
    ( sK4 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | sK3 = k2_mcart_1(sK4) ),
    inference(resolution,[],[f94,f97])).

fof(f97,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f43,f86])).

fof(f86,plain,(
    sK7(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( sK4 != sK4
    | sK7(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(superposition,[],[f70,f64])).

fof(f70,plain,(
    ! [X14,X12,X13] :
      ( sK4 != k3_mcart_1(X12,X13,X14)
      | sK7(sK0,sK1,sK2,sK4) = X14 ) ),
    inference(superposition,[],[f26,f46])).

fof(f46,plain,(
    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f45,f15])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f44,f17])).

fof(f44,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f32,f16])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f43,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    inference(subsumption_resolution,[],[f42,f15])).

fof(f42,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    inference(subsumption_resolution,[],[f41,f17])).

fof(f41,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    inference(subsumption_resolution,[],[f31,f16])).

fof(f31,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) ),
    inference(resolution,[],[f14,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),X0)
      | sK3 = X0 ) ),
    inference(backward_demodulation,[],[f89,f87])).

fof(f87,plain,(
    sK6(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( sK4 != sK4
    | sK6(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f68,f64])).

fof(f68,plain,(
    ! [X6,X8,X7] :
      ( sK4 != k3_mcart_1(X6,X7,X8)
      | sK6(sK0,sK1,sK2,sK4) = X7 ) ),
    inference(superposition,[],[f25,f46])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0] :
      ( sK4 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),sK6(sK0,sK1,sK2,sK4),X0)
      | ~ m1_subset_1(X0,sK2)
      | sK3 = X0 ) ),
    inference(backward_demodulation,[],[f76,f88])).

fof(f88,plain,(
    sK5(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( sK4 != sK4
    | sK5(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f66,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_mcart_1(X0,X1,X2) != sK4
      | sK5(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(superposition,[],[f24,f46])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),X0)
      | sK3 = X0 ) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(subsumption_resolution,[],[f48,f15])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f47,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(subsumption_resolution,[],[f33,f16])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(X1,sK2)
      | sK4 != k3_mcart_1(sK5(sK0,sK1,sK2,sK4),X0,X1)
      | sK3 = X1 ) ),
    inference(resolution,[],[f52,f13])).

fof(f13,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f51,f15])).

fof(f51,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f50,f17])).

fof(f50,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f34,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(resolution,[],[f14,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (17901)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (17896)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (17915)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (17899)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (17898)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (17919)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (17902)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (17917)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (17906)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (17899)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f101,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    sK3 != k2_mcart_1(sK4)),
% 0.20/0.51    inference(superposition,[],[f18,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f62,f15])).
% 0.20/0.51  % (17908)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.51    inference(flattening,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f61,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    k1_xboole_0 != sK2),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f37,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    k1_xboole_0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.51    inference(resolution,[],[f14,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    sK3 = k2_mcart_1(sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))),
% 0.20/0.51    inference(backward_demodulation,[],[f60,f63])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(backward_demodulation,[],[f56,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f58,f15])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f57,f17])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f36,f16])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(resolution,[],[f14,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    sK4 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(backward_demodulation,[],[f40,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f54,f15])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f53,f17])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f35,f16])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(resolution,[],[f14,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f39,f15])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f38,f17])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f30,f16])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK4),k6_mcart_1(sK0,sK1,sK2,sK4),k7_mcart_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(resolution,[],[f14,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    sK4 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4)),
% 0.20/0.51    inference(resolution,[],[f94,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.20/0.51    inference(backward_demodulation,[],[f43,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    sK7(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    sK4 != sK4 | sK7(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.20/0.51    inference(superposition,[],[f70,f64])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X14,X12,X13] : (sK4 != k3_mcart_1(X12,X13,X14) | sK7(sK0,sK1,sK2,sK4) = X14) )),
% 0.20/0.51    inference(superposition,[],[f26,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f45,f15])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f44,f17])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f32,f16])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))),
% 0.20/0.51    inference(resolution,[],[f14,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X2 = X5) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f42,f15])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f41,f17])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f31,f16])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)),
% 0.20/0.51    inference(resolution,[],[f14,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK4 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)),X0) | sK3 = X0) )),
% 0.20/0.51    inference(backward_demodulation,[],[f89,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    sK6(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    sK4 != sK4 | sK6(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(superposition,[],[f68,f64])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (sK4 != k3_mcart_1(X6,X7,X8) | sK6(sK0,sK1,sK2,sK4) = X7) )),
% 0.20/0.51    inference(superposition,[],[f25,f46])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X1 = X4) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0] : (sK4 != k3_mcart_1(k1_mcart_1(k1_mcart_1(sK4)),sK6(sK0,sK1,sK2,sK4),X0) | ~m1_subset_1(X0,sK2) | sK3 = X0) )),
% 0.20/0.51    inference(backward_demodulation,[],[f76,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    sK5(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    sK4 != sK4 | sK5(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.51    inference(superposition,[],[f66,f64])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK4 | sK5(sK0,sK1,sK2,sK4) = X0) )),
% 0.20/0.51    inference(superposition,[],[f24,f46])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X0 = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK4 != k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),X0) | sK3 = X0) )),
% 0.20/0.51    inference(resolution,[],[f65,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f48,f15])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f47,f17])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f33,f16])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.20/0.51    inference(resolution,[],[f14,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X1,sK2) | sK4 != k3_mcart_1(sK5(sK0,sK1,sK2,sK4),X0,X1) | sK3 = X1) )),
% 0.20/0.51    inference(resolution,[],[f52,f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f51,f15])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f50,f17])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f34,f16])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.20/0.51    inference(resolution,[],[f14,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | m1_subset_1(sK5(X0,X1,X2,X3),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (17899)------------------------------
% 0.20/0.51  % (17899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17899)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (17899)Memory used [KB]: 6140
% 0.20/0.51  % (17899)Time elapsed: 0.101 s
% 0.20/0.51  % (17899)------------------------------
% 0.20/0.51  % (17899)------------------------------
% 0.20/0.51  % (17916)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (17893)Success in time 0.157 s
%------------------------------------------------------------------------------
