%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 391 expanded)
%              Number of leaves         :    7 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  252 (3190 expanded)
%              Number of equality atoms :  174 (1978 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f65])).

fof(f65,plain,(
    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5)) ),
    inference(backward_demodulation,[],[f60,f64])).

fof(f64,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f63,plain,
    ( k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f61,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f37,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(resolution,[],[f18,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f18,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(backward_demodulation,[],[f55,f59])).

fof(f59,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f58,f22])).

fof(f58,plain,
    ( k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f57,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f56,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f36,f19])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(backward_demodulation,[],[f50,f54])).

fof(f54,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f53,f22])).

fof(f53,plain,
    ( k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f52,f21])).

fof(f52,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f35,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(backward_demodulation,[],[f45,f49])).

fof(f49,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f48,plain,
    ( k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f47,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f46,f20])).

% (26669)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f46,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(resolution,[],[f18,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f44,f22])).

fof(f44,plain,
    ( k1_xboole_0 = sK3
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f43,f21])).

fof(f43,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f42,f20])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f33,f19])).

fof(f33,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f18,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f105,plain,(
    sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5)) ),
    inference(resolution,[],[f100,f69])).

fof(f69,plain,(
    m1_subset_1(k2_mcart_1(sK5),sK3) ),
    inference(subsumption_resolution,[],[f67,f18])).

fof(f67,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f29,f64])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f100,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,sK3)
      | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),X20) ) ),
    inference(subsumption_resolution,[],[f99,f70])).

fof(f70,plain,(
    sK4 != k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[],[f23,f59])).

fof(f23,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,sK3)
      | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),X20)
      | sK4 = k2_mcart_1(k1_mcart_1(sK5)) ) ),
    inference(resolution,[],[f94,f73])).

fof(f73,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) ),
    inference(subsumption_resolution,[],[f71,f18])).

fof(f71,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f32,f59])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f94,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,sK2)
      | ~ m1_subset_1(X25,sK3)
      | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),X24,X25)
      | sK4 = X24 ) ),
    inference(resolution,[],[f81,f84])).

fof(f84,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) ),
    inference(subsumption_resolution,[],[f82,f18])).

fof(f82,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f31,f54])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(X2,sK3)
      | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),X0,X1,X2)
      | sK4 = X1 ) ),
    inference(resolution,[],[f80,f17])).

fof(f17,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) ),
    inference(subsumption_resolution,[],[f78,f18])).

fof(f78,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f30,f49])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:40:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (26674)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (26665)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (26677)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (26674)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))),
% 0.20/0.48    inference(backward_demodulation,[],[f60,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f63,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    k1_xboole_0 != sK3),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f62,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k1_xboole_0 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f61,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f37,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 0.20/0.48    inference(resolution,[],[f18,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(backward_demodulation,[],[f55,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f58,f22])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f57,f21])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f56,f20])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f36,f19])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.48    inference(resolution,[],[f18,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(backward_demodulation,[],[f50,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f53,f22])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f52,f21])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f51,f20])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f35,f19])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(resolution,[],[f18,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(backward_demodulation,[],[f45,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f48,f22])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f47,f21])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f46,f20])).
% 0.20/0.48  % (26669)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f34,f19])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.20/0.48    inference(resolution,[],[f18,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f44,f22])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f43,f21])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f42,f20])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(subsumption_resolution,[],[f33,f19])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK5 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),k10_mcart_1(sK0,sK1,sK2,sK3,sK5),k11_mcart_1(sK0,sK1,sK2,sK3,sK5))),
% 0.20/0.48    inference(resolution,[],[f18,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(sK5))),
% 0.20/0.48    inference(resolution,[],[f100,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(k2_mcart_1(sK5),sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f67,f18])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    m1_subset_1(k2_mcart_1(sK5),sK3) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.48    inference(superposition,[],[f29,f64])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X20] : (~m1_subset_1(X20,sK3) | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),X20)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f99,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    sK4 != k2_mcart_1(k1_mcart_1(sK5))),
% 0.20/0.48    inference(superposition,[],[f23,f59])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X20] : (~m1_subset_1(X20,sK3) | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(sK5)),X20) | sK4 = k2_mcart_1(k1_mcart_1(sK5))) )),
% 0.20/0.48    inference(resolution,[],[f94,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f71,f18])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.48    inference(superposition,[],[f32,f59])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X24,X25] : (~m1_subset_1(X24,sK2) | ~m1_subset_1(X25,sK3) | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),X24,X25) | sK4 = X24) )),
% 0.20/0.48    inference(resolution,[],[f81,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f82,f18])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.49    inference(superposition,[],[f31,f54])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X1,sK2) | ~m1_subset_1(X2,sK3) | sK5 != k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),X0,X1,X2) | sK4 = X1) )),
% 0.20/0.49    inference(resolution,[],[f80,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X8) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f18])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.49    inference(superposition,[],[f30,f49])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (26674)------------------------------
% 0.20/0.49  % (26674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (26674)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (26674)Memory used [KB]: 1791
% 0.20/0.49  % (26674)Time elapsed: 0.057 s
% 0.20/0.49  % (26674)------------------------------
% 0.20/0.49  % (26674)------------------------------
% 0.20/0.49  % (26660)Success in time 0.127 s
%------------------------------------------------------------------------------
