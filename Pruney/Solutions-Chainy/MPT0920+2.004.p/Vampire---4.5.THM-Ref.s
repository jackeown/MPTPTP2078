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
% DateTime   : Thu Dec  3 12:59:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 (1925 expanded)
%              Number of leaves         :    8 ( 421 expanded)
%              Depth                    :   28
%              Number of atoms          :  441 (12829 expanded)
%              Number of equality atoms :  329 (8152 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f241])).

fof(f241,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f158,f158])).

fof(f158,plain,(
    ! [X0] : k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ),
    inference(subsumption_resolution,[],[f157,f22])).

fof(f22,plain,(
    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f11])).

% (26394)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                           => X4 = X7 ) ) ) ) )
         => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f157,plain,(
    ! [X0] :
      ( sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f156,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f156,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f155,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f155,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK0
      | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f154,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f154,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK0
      | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f153,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f153,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK0
      | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(resolution,[],[f144,f43])).

fof(f43,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f17,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f144,plain,(
    ! [X35,X33,X31,X34,X32] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X32,X33),X34),X35))
      | k1_xboole_0 = X33
      | k1_xboole_0 = X34
      | k1_xboole_0 = X35
      | k1_xboole_0 = X32
      | sK4 = k9_mcart_1(X32,X33,X34,X35,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X31 ) ),
    inference(superposition,[],[f61,f137])).

fof(f137,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(superposition,[],[f113,f133])).

fof(f133,plain,(
    ! [X46] :
      ( sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46 ) ),
    inference(subsumption_resolution,[],[f132,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f88,f83])).

fof(f83,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f82,f18])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f81,f21])).

fof(f81,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f80,f20])).

fof(f80,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f79,f19])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
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

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f21])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f20])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f19])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f84,f18])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f132,plain,(
    ! [X46] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0)
      | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46 ) ),
    inference(subsumption_resolution,[],[f131,f107])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f106,f83])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f21])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f104,f20])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f103,f19])).

fof(f103,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f102,f18])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f58,f43])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f131,plain,(
    ! [X46] :
      ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0)
      | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46 ) ),
    inference(subsumption_resolution,[],[f130,f101])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f100,f83])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f99,f21])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f98,f20])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f97,f19])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f96,f18])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f130,plain,(
    ! [X46] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X46,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0)
      | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46 ) ),
    inference(subsumption_resolution,[],[f129,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f94,f83])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f92,f20])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f90,f18])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,(
    ! [X46] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X46,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X46,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0)
      | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46 ) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,(
    ! [X46] :
      ( sK5 != sK5
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X46,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X46,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0)
      | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46 ) ),
    inference(superposition,[],[f44,f113])).

fof(f44,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X7 ) ),
    inference(definition_unfolding,[],[f16,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f16,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X7 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f113,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f112,f83])).

fof(f112,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f111,f21])).

fof(f111,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f110,f20])).

fof(f110,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f109,f19])).

fof(f109,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f108,f18])).

fof(f108,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5)),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f36,f42,f41])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(definition_unfolding,[],[f32,f42,f41])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              | k4_mcart_1(X5,X6,X7,X8) != X4 )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

% (26420)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (26396)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (26395)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (26403)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (26402)Refutation not found, incomplete strategy% (26402)------------------------------
% (26402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26403)Refutation not found, incomplete strategy% (26403)------------------------------
% (26403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26403)Termination reason: Refutation not found, incomplete strategy

% (26403)Memory used [KB]: 10618
% (26403)Time elapsed: 0.124 s
% (26403)------------------------------
% (26403)------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f243,plain,(
    sK4 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(superposition,[],[f22,f158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (26399)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (26397)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (26398)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (26409)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (26402)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (26416)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (26415)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (26408)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (26407)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (26408)Refutation not found, incomplete strategy% (26408)------------------------------
% 0.22/0.53  % (26408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26408)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26408)Memory used [KB]: 6140
% 0.22/0.53  % (26408)Time elapsed: 0.004 s
% 0.22/0.53  % (26408)------------------------------
% 0.22/0.53  % (26408)------------------------------
% 0.22/0.53  % (26400)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (26399)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f243,f241])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 = X1) )),
% 0.22/0.54    inference(superposition,[],[f158,f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ( ! [X0] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f157,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  % (26394)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(flattening,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f8])).
% 0.22/0.54  fof(f8,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ( ! [X0] : (sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = sK0 | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f155,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    k1_xboole_0 != sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f154,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    k1_xboole_0 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f153,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(resolution,[],[f144,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.22/0.54    inference(definition_unfolding,[],[f17,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X35,X33,X31,X34,X32] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X32,X33),X34),X35)) | k1_xboole_0 = X33 | k1_xboole_0 = X34 | k1_xboole_0 = X35 | k1_xboole_0 = X32 | sK4 = k9_mcart_1(X32,X33,X34,X35,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X31) )),
% 0.22/0.54    inference(superposition,[],[f61,f137])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f134])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK4),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(superposition,[],[f113,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X46] : (sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f132,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f88,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f82,f18])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f81,f21])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f80,f20])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f79,f19])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(resolution,[],[f48,f43])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f27,f42])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f87,f21])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f20])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f85,f19])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f84,f18])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(resolution,[],[f53,f43])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f40,f42])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X46] : (~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0) | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f106,f83])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f105,f21])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f104,f20])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f103,f19])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f102,f18])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(resolution,[],[f58,f43])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f42])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X46] : (~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0) | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f130,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f100,f83])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f21])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f20])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f97,f19])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f96,f18])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(resolution,[],[f55,f43])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f42])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ( ! [X46] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X46,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0) | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f129,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f94,f83])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f93,f21])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f92,f20])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f91,f19])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f90,f18])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(resolution,[],[f54,f43])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f39,f42])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    ( ! [X46] : (~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X46,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X46,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0) | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46) )),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f123])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X46] : (sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X46,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X46,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X46,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X46,sK5),sK0) | sK4 = sK7(sK0,sK1,sK2,sK3,X46,sK5) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X46) )),
% 0.22/0.54    inference(superposition,[],[f44,f113])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X7) )),
% 0.22/0.54    inference(definition_unfolding,[],[f16,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X7) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f112,f83])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f111,f21])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f110,f20])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f109,f19])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f108,f18])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X0] : (sK5 = k4_tarski(k4_tarski(k4_tarski(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5)),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.22/0.54    inference(resolution,[],[f57,f43])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5)),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f36,f42,f41])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6) )),
% 0.22/0.54    inference(equality_resolution,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.22/0.54    inference(definition_unfolding,[],[f32,f42,f41])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  % (26420)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (26396)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (26395)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (26403)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (26402)Refutation not found, incomplete strategy% (26402)------------------------------
% 0.22/0.54  % (26402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26403)Refutation not found, incomplete strategy% (26403)------------------------------
% 0.22/0.54  % (26403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26403)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26403)Memory used [KB]: 10618
% 0.22/0.54  % (26403)Time elapsed: 0.124 s
% 0.22/0.54  % (26403)------------------------------
% 0.22/0.54  % (26403)------------------------------
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    sK4 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 0.22/0.54    inference(superposition,[],[f22,f158])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (26399)------------------------------
% 0.22/0.54  % (26399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26399)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (26399)Memory used [KB]: 6396
% 0.22/0.54  % (26399)Time elapsed: 0.101 s
% 0.22/0.54  % (26399)------------------------------
% 0.22/0.54  % (26399)------------------------------
% 0.22/0.54  % (26421)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (26392)Success in time 0.181 s
%------------------------------------------------------------------------------
