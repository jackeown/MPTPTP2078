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
% DateTime   : Thu Dec  3 12:59:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 471 expanded)
%              Number of leaves         :    6 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  240 (2653 expanded)
%              Number of equality atoms :  144 (1657 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(global_subsumption,[],[f93,f98,f103])).

fof(f103,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(subsumption_resolution,[],[f102,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f102,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f101,f29])).

fof(f29,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f13,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f13,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f100,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f99,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f87])).

fof(f87,plain,(
    k1_mcart_1(k1_mcart_1(sK4)) = sK5(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f18,f70])).

fof(f70,plain,(
    k1_mcart_1(sK4) = k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)) ),
    inference(superposition,[],[f18,f66])).

fof(f66,plain,(
    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f65,f14])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f64,f16])).

% (2272)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f64,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f60,f15])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(resolution,[],[f36,f29])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(definition_unfolding,[],[f26,f21,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f18,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f98,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(subsumption_resolution,[],[f97,f14])).

fof(f97,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f96,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f95,f16])).

fof(f95,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f94,f15])).

fof(f94,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f86])).

fof(f86,plain,(
    k2_mcart_1(k1_mcart_1(sK4)) = sK6(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f19,f70])).

fof(f19,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(backward_demodulation,[],[f89,f87])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(backward_demodulation,[],[f88,f86])).

fof(f88,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(global_subsumption,[],[f76,f84])).

fof(f84,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f83,f14])).

fof(f83,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f81,f16])).

fof(f81,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f80,f15])).

fof(f80,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f37,f69])).

fof(f69,plain,(
    k2_mcart_1(sK4) = sK7(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f19,f66])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(forward_demodulation,[],[f75,f69])).

fof(f75,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f73,f45])).

fof(f45,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f17,f44])).

fof(f44,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f43,f14])).

fof(f43,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f42,f16])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f38,f15])).

fof(f38,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f17,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(backward_demodulation,[],[f71,f69])).

fof(f71,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)
    | sK3 = sK7(sK0,sK1,sK2,sK4) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( sK4 != sK4
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)
    | sK3 = sK7(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f30,f66])).

fof(f30,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f12,f20])).

fof(f12,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:15:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (2273)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (2290)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (2282)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (2288)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (2274)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (2273)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (2290)Refutation not found, incomplete strategy% (2290)------------------------------
% 0.21/0.51  % (2290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2290)Memory used [KB]: 1791
% 0.21/0.51  % (2290)Time elapsed: 0.053 s
% 0.21/0.51  % (2290)------------------------------
% 0.21/0.51  % (2290)------------------------------
% 0.21/0.51  % (2281)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (2267)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f93,f98,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f13,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f34,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k1_mcart_1(k1_mcart_1(sK4)) = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(superposition,[],[f18,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    k1_mcart_1(sK4) = k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4))),
% 0.21/0.52    inference(superposition,[],[f18,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.52    inference(subsumption_resolution,[],[f65,f14])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.52    inference(subsumption_resolution,[],[f64,f16])).
% 0.21/0.52  % (2272)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.52    inference(subsumption_resolution,[],[f60,f15])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.52    inference(resolution,[],[f36,f29])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f21,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f21])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK5(X0,X1,X2,X3),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f14])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f29])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f16])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f15])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f35,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k2_mcart_1(k1_mcart_1(sK4)) = sK6(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(superposition,[],[f19,f70])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f21])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK6(X0,X1,X2,X3),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f89,f87])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f88,f86])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(global_subsumption,[],[f76,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f83,f14])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f29])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f16])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f15])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f37,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k2_mcart_1(sK4) = sK7(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(superposition,[],[f19,f66])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f21])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK7(X0,X1,X2,X3),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f75,f69])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    sK3 != k2_mcart_1(sK4)),
% 0.21/0.52    inference(superposition,[],[f17,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f43,f14])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f42,f16])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f38,f15])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f31,f29])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f21])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    sK3 = k2_mcart_1(sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f71,f69])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    sK4 != sK4 | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(superposition,[],[f30,f66])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.21/0.52    inference(definition_unfolding,[],[f12,f20])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2273)------------------------------
% 0.21/0.52  % (2273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2273)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2273)Memory used [KB]: 6396
% 0.21/0.52  % (2273)Time elapsed: 0.100 s
% 0.21/0.52  % (2273)------------------------------
% 0.21/0.52  % (2273)------------------------------
% 0.21/0.52  % (2270)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (2266)Success in time 0.156 s
%------------------------------------------------------------------------------
