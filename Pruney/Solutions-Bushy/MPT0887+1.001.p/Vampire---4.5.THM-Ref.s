%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0887+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 111 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  233 ( 603 expanded)
%              Number of equality atoms :  171 ( 494 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f95])).

% (18389)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (18372)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (18390)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f95,plain,(
    sK6 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( sK5 != sK5
    | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f84,f90])).

fof(f90,plain,(
    sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f89,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) != X6
                | k6_mcart_1(X0,X1,X2,X3) != X5
                | k5_mcart_1(X0,X1,X2,X3) != X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ? [X3] :
              ( ? [X4,X5,X6] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                      & k6_mcart_1(X0,X1,X2,X3) = X5
                      & k5_mcart_1(X0,X1,X2,X3) = X4 )
                  & k3_mcart_1(X4,X5,X6) = X3 )
              & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f88,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f87,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

% (18388)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f87,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f44,f18])).

fof(f18,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | sK5 = k6_mcart_1(X3,X4,X5,sK3) ) ),
    inference(subsumption_resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f41,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k6_mcart_1(X3,X4,X5,sK3),X4)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | ~ m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5))
      | k1_xboole_0 = X3
      | sK5 = k6_mcart_1(X3,X4,X5,sK3) ) ),
    inference(superposition,[],[f37,f17])).

fof(f17,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X6 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X1)
      | X4 = X6
      | k6_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) != X4 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X1)
      | k3_mcart_1(X5,X6,X7) != X3
      | X4 = X6
      | k6_mcart_1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k6_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X6
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X1) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( k6_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X6 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).

fof(f84,plain,
    ( sK6 != k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( sK4 != sK4
    | sK6 != k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f16,f79])).

fof(f79,plain,(
    sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f78,f19])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f77,f20])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f76,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK4 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f43,f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK4 = k5_mcart_1(X0,X1,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k5_mcart_1(X0,X1,X2,sK3),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | sK4 = k5_mcart_1(X0,X1,X2,sK3) ) ),
    inference(superposition,[],[f39,f17])).

fof(f39,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X5 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X0)
      | X4 = X5
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) != X4 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X0)
      | k3_mcart_1(X5,X6,X7) != X3
      | X4 = X5
      | k5_mcart_1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

fof(f16,plain,
    ( sK6 != k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK5 != k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK4 != k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f100,f19])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f99,f20])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f98,f21])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK6 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f45,f18])).

fof(f45,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8))
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | sK6 = k7_mcart_1(X6,X7,X8,sK3) ) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f42,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(k7_mcart_1(X6,X7,X8,sK3),X8)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X8
      | ~ m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8))
      | k1_xboole_0 = X6
      | sK6 = k7_mcart_1(X6,X7,X8,sK3) ) ),
    inference(superposition,[],[f35,f17])).

fof(f35,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) = X7 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k3_mcart_1(X5,X6,X7),k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X2)
      | X4 = X7
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X5,X6,X7)) != X4 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | ~ m1_subset_1(X4,X2)
      | k3_mcart_1(X5,X6,X7) != X3
      | X4 = X7
      | k7_mcart_1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X7
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ( k7_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X7 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_mcart_1)).

%------------------------------------------------------------------------------
