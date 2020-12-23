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
% DateTime   : Thu Dec  3 12:59:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 711 expanded)
%              Number of leaves         :    6 ( 153 expanded)
%              Depth                    :   27
%              Number of atoms          :  392 (4929 expanded)
%              Number of equality atoms :  287 (3082 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f105])).

fof(f105,plain,(
    ! [X0] : k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ),
    inference(subsumption_resolution,[],[f104,f20])).

fof(f20,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f104,plain,(
    ! [X0] :
      ( sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f103,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f102,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f101,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f100,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f98,f35])).

fof(f35,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f15,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f15,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X14,X12,X15,X13,X11] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15))
      | k1_xboole_0 = X12
      | k1_xboole_0 = X13
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X11 ) ),
    inference(superposition,[],[f48,f94])).

fof(f94,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(superposition,[],[f64,f90])).

fof(f90,plain,(
    ! [X0] :
      ( sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f80])).

fof(f80,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f79,f19])).

fof(f79,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f78,f18])).

fof(f78,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f77,f17])).

fof(f77,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(subsumption_resolution,[],[f56,f16])).

fof(f56,plain,(
    ! [X5] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(resolution,[],[f35,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f88,f60])).

% (19044)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (19037)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (19044)Refutation not found, incomplete strategy% (19044)------------------------------
% (19044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19044)Termination reason: Refutation not found, incomplete strategy

% (19044)Memory used [KB]: 10618
% (19044)Time elapsed: 0.128 s
% (19044)------------------------------
% (19044)------------------------------
fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f59,f19])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f57,f17])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f51,f16])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f72])).

fof(f72,plain,(
    ! [X3] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3 ) ),
    inference(subsumption_resolution,[],[f71,f19])).

fof(f71,plain,(
    ! [X3] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3 ) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,(
    ! [X3] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3 ) ),
    inference(subsumption_resolution,[],[f69,f17])).

fof(f69,plain,(
    ! [X3] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3 ) ),
    inference(subsumption_resolution,[],[f54,f16])).

fof(f54,plain,(
    ! [X3] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3 ) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f76])).

fof(f76,plain,(
    ! [X4] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f75,plain,(
    ! [X4] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f74,f18])).

fof(f74,plain,(
    ! [X4] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f73,f17])).

fof(f73,plain,(
    ! [X4] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(subsumption_resolution,[],[f55,f16])).

fof(f55,plain,(
    ! [X4] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4 ) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( sK5 != sK5
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(superposition,[],[f36,f64])).

fof(f36,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X8 ) ),
    inference(definition_unfolding,[],[f14,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f14,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X1] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f63,f19])).

fof(f63,plain,(
    ! [X1] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5))
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f62,f18])).

fof(f62,plain,(
    ! [X1] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f61,f17])).

fof(f61,plain,(
    ! [X1] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(subsumption_resolution,[],[f52,f16])).

fof(f52,plain,(
    ! [X1] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1 ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f29,f34,f22])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X7 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f26,f34,f22])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f127,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f20,f105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19025)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (19030)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (19039)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (19055)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (19025)Refutation not found, incomplete strategy% (19025)------------------------------
% 0.20/0.51  % (19025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19025)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19025)Memory used [KB]: 1663
% 0.20/0.51  % (19025)Time elapsed: 0.102 s
% 0.20/0.51  % (19025)------------------------------
% 0.20/0.51  % (19025)------------------------------
% 0.20/0.52  % (19050)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (19040)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (19048)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (19033)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (19028)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (19031)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (19042)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (19056)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (19042)Refutation not found, incomplete strategy% (19042)------------------------------
% 0.20/0.53  % (19042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19042)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19042)Memory used [KB]: 6140
% 0.20/0.53  % (19042)Time elapsed: 0.001 s
% 0.20/0.53  % (19042)------------------------------
% 0.20/0.53  % (19042)------------------------------
% 0.20/0.53  % (19054)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (19029)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (19027)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (19032)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (19053)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (19026)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (19048)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f127,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f104,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f6])).
% 0.20/0.54  fof(f6,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ( ! [X0] : (sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f103,f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    k1_xboole_0 != sK3),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK3 | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f102,f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    k1_xboole_0 != sK2),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f101,f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f100,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    k1_xboole_0 != sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(resolution,[],[f98,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.20/0.54    inference(definition_unfolding,[],[f15,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f23,f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X14,X12,X15,X13,X11] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15)) | k1_xboole_0 = X12 | k1_xboole_0 = X13 | k1_xboole_0 = X14 | k1_xboole_0 = X15 | sK4 = k10_mcart_1(X12,X13,X14,X15,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X11) )),
% 0.20/0.54    inference(superposition,[],[f48,f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(superposition,[],[f64,f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X0] : (sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f89,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X5] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f79,f19])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X5] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f78,f18])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X5] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f77,f17])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X5] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f56,f16])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X5] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X5,sK5),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 0.20/0.54    inference(resolution,[],[f35,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f33,f34])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f88,f60])).
% 0.20/0.54  % (19044)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (19037)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (19044)Refutation not found, incomplete strategy% (19044)------------------------------
% 0.20/0.54  % (19044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19044)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19044)Memory used [KB]: 10618
% 0.20/0.54  % (19044)Time elapsed: 0.128 s
% 0.20/0.54  % (19044)------------------------------
% 0.20/0.54  % (19044)------------------------------
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f59,f19])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f58,f18])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f57,f17])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f51,f16])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(resolution,[],[f35,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f28,f34])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f87,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X3] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f71,f19])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X3] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f70,f18])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X3] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f69,f17])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X3] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f54,f16])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X3] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X3,sK5),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X3) )),
% 0.20/0.54    inference(resolution,[],[f35,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f31,f34])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f86,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X4] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f75,f19])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X4] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f74,f18])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X4] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f73,f17])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X4] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f55,f16])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X4] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X4,sK5),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X4) )),
% 0.20/0.54    inference(resolution,[],[f35,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f32,f34])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | sK4 = sK8(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(superposition,[],[f36,f64])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X8) )),
% 0.20/0.54    inference(definition_unfolding,[],[f14,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X8) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X1] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f63,f19])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X1] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f62,f18])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X1] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f61,f17])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X1] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f52,f16])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X1] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X1,sK5),sK7(sK0,sK1,sK2,sK3,X1,sK5),sK8(sK0,sK1,sK2,sK3,X1,sK5)),sK9(sK0,sK1,sK2,sK3,X1,sK5)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X1) )),
% 0.20/0.54    inference(resolution,[],[f35,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f29,f34,f22])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X7) )),
% 0.20/0.54    inference(equality_resolution,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.20/0.54    inference(definition_unfolding,[],[f26,f34,f22])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.54    inference(superposition,[],[f20,f105])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (19048)------------------------------
% 0.20/0.54  % (19048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19048)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (19048)Memory used [KB]: 1791
% 0.20/0.54  % (19048)Time elapsed: 0.123 s
% 0.20/0.54  % (19048)------------------------------
% 0.20/0.54  % (19048)------------------------------
% 0.20/0.54  % (19049)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (19020)Success in time 0.183 s
%------------------------------------------------------------------------------
