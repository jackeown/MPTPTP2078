%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 (1736 expanded)
%              Number of leaves         :    5 ( 349 expanded)
%              Depth                    :   41
%              Number of atoms          :  492 (13267 expanded)
%              Number of equality atoms :  371 (8419 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(subsumption_resolution,[],[f192,f189])).

fof(f189,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f129,f129])).

fof(f129,plain,(
    ! [X0] : k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ),
    inference(subsumption_resolution,[],[f128,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f128,plain,(
    ! [X0] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f127,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f127,plain,(
    ! [X0] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f126,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f126,plain,(
    ! [X0] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f125,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f125,plain,(
    ! [X0] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f124,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f14,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

% (27814)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f124,plain,(
    ! [X0] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0] :
      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f122,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f29,f21])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f121,f18])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f120,f17])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f119,f16])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f118,f15])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(subsumption_resolution,[],[f117,f32])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f115,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f114,f82])).

fof(f82,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f81,f18])).

fof(f81,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f80,f17])).

fof(f80,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f79,f16])).

fof(f79,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f78,f15])).

fof(f78,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f75,f32])).

fof(f75,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2] :
      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(superposition,[],[f38,f71])).

fof(f71,plain,(
    ! [X0] :
      ( sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f69,f17])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f68,f16])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f67,f15])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f57,f32])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X4
      | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(X1,X2,X3,X4,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(superposition,[],[f47,f56])).

fof(f56,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f55,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f54,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f53,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f48,f15])).

fof(f48,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f27,f21,f20])).

% (27816)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(definition_unfolding,[],[f22,f21,f20])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f10])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

% (27803)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (27804)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (27813)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (27804)Refutation not found, incomplete strategy% (27804)------------------------------
% (27804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27804)Termination reason: Refutation not found, incomplete strategy

% (27804)Memory used [KB]: 10618
% (27804)Time elapsed: 0.139 s
% (27804)------------------------------
% (27804)------------------------------
% (27800)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (27807)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (27815)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (27790)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (27796)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (27813)Refutation not found, incomplete strategy% (27813)------------------------------
% (27813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27797)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (27796)Refutation not found, incomplete strategy% (27796)------------------------------
% (27796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27796)Termination reason: Refutation not found, incomplete strategy

% (27796)Memory used [KB]: 10618
% (27796)Time elapsed: 0.140 s
% (27796)------------------------------
% (27796)------------------------------
% (27808)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (27797)Refutation not found, incomplete strategy% (27797)------------------------------
% (27797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27797)Termination reason: Refutation not found, incomplete strategy

% (27797)Memory used [KB]: 10618
% (27797)Time elapsed: 0.141 s
% (27797)------------------------------
% (27797)------------------------------
% (27813)Termination reason: Refutation not found, incomplete strategy

% (27813)Memory used [KB]: 10874
% (27813)Time elapsed: 0.141 s
% (27813)------------------------------
% (27813)------------------------------
fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f31,f21])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f114,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f113,f106])).

fof(f106,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f105,f18])).

fof(f105,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f104,f17])).

fof(f104,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f103,f16])).

fof(f103,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f102,f15])).

fof(f102,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2] :
      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 ) ),
    inference(superposition,[],[f39,f95])).

fof(f95,plain,(
    ! [X0] :
      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f18])).

fof(f94,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f93,f17])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f92,f16])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f15])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f58,f32])).

fof(f58,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X6,X7,X8),X9))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X8
      | k1_xboole_0 = X9
      | sK7(sK0,sK1,sK2,sK3,X5,sK5) = k9_mcart_1(X6,X7,X8,X9,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5 ) ),
    inference(superposition,[],[f46,f56])).

fof(f46,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X6 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(definition_unfolding,[],[f23,f21,f20])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | ~ m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f30,f21])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f113,plain,(
    ! [X20] :
      ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(subsumption_resolution,[],[f112,f19])).

fof(f19,plain,(
    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f112,plain,(
    ! [X20] :
      ( ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,(
    ! [X20] :
      ( sK5 != sK5
      | ~ m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0)
      | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20 ) ),
    inference(superposition,[],[f33,f101])).

fof(f101,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(superposition,[],[f77,f95])).

fof(f77,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(superposition,[],[f56,f71])).

fof(f33,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X7 ) ),
    inference(definition_unfolding,[],[f13,f20])).

fof(f13,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X7 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f192,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f19,f129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (27787)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (27789)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (27791)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (27798)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (27809)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (27801)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (27788)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (27798)Refutation not found, incomplete strategy% (27798)------------------------------
% 0.20/0.53  % (27798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27798)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27798)Memory used [KB]: 10618
% 0.20/0.53  % (27798)Time elapsed: 0.117 s
% 0.20/0.53  % (27798)------------------------------
% 0.20/0.53  % (27798)------------------------------
% 0.20/0.53  % (27793)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (27792)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (27799)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (27787)Refutation not found, incomplete strategy% (27787)------------------------------
% 0.20/0.53  % (27787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27787)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27787)Memory used [KB]: 1663
% 0.20/0.53  % (27787)Time elapsed: 0.117 s
% 0.20/0.53  % (27787)------------------------------
% 0.20/0.53  % (27787)------------------------------
% 0.20/0.53  % (27802)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (27810)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (27795)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (27802)Refutation not found, incomplete strategy% (27802)------------------------------
% 0.20/0.54  % (27802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27802)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27802)Memory used [KB]: 6140
% 0.20/0.54  % (27802)Time elapsed: 0.004 s
% 0.20/0.54  % (27802)------------------------------
% 0.20/0.54  % (27802)------------------------------
% 0.20/0.54  % (27794)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (27811)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (27806)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (27812)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (27805)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (27793)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f192,f189])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ( ! [X0,X1] : (X0 = X1) )),
% 0.20/0.54    inference(superposition,[],[f129,f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f128,f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    k1_xboole_0 != sK3),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f7])).
% 0.20/0.54  fof(f7,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f5])).
% 0.20/0.54  fof(f5,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f127,f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    k1_xboole_0 != sK2),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f126,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f125,f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    k1_xboole_0 != sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f124,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3))),
% 0.20/0.54    inference(definition_unfolding,[],[f14,f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  % (27814)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ( ! [X0] : (k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(resolution,[],[f122,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f29,f21])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X6 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f121,f18])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f120,f17])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f119,f16])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f118,f15])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f117,f32])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(resolution,[],[f115,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f26,f21])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ( ! [X20] : (~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f114,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f81,f18])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f80,f17])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f79,f16])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f78,f15])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f75,f32])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X2] : (m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.54    inference(superposition,[],[f38,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0] : (sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f70,f18])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK3 | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f69,f17])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f68,f16])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f67,f15])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(resolution,[],[f57,f32])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X4 | sK6(sK0,sK1,sK2,sK3,X0,sK5) = k8_mcart_1(X1,X2,X3,X4,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(superposition,[],[f47,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f55,f18])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f54,f17])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f53,f16])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f48,f15])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.54    inference(resolution,[],[f42,f32])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k4_tarski(k3_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5)),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(definition_unfolding,[],[f27,f21,f20])).
% 0.20/0.54  % (27816)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X5) )),
% 0.20/0.54    inference(equality_resolution,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.20/0.54    inference(definition_unfolding,[],[f22,f21,f20])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(flattening,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  % (27803)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (27804)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (27813)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (27804)Refutation not found, incomplete strategy% (27804)------------------------------
% 0.20/0.55  % (27804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27804)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27804)Memory used [KB]: 10618
% 0.20/0.55  % (27804)Time elapsed: 0.139 s
% 0.20/0.55  % (27804)------------------------------
% 0.20/0.55  % (27804)------------------------------
% 0.20/0.55  % (27800)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (27807)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (27815)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (27790)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (27796)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (27813)Refutation not found, incomplete strategy% (27813)------------------------------
% 0.20/0.55  % (27813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27797)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (27796)Refutation not found, incomplete strategy% (27796)------------------------------
% 0.20/0.55  % (27796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27796)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27796)Memory used [KB]: 10618
% 0.20/0.55  % (27796)Time elapsed: 0.140 s
% 0.20/0.55  % (27796)------------------------------
% 0.20/0.55  % (27796)------------------------------
% 0.20/0.55  % (27808)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (27797)Refutation not found, incomplete strategy% (27797)------------------------------
% 0.20/0.55  % (27797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27797)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27797)Memory used [KB]: 10618
% 0.20/0.55  % (27797)Time elapsed: 0.141 s
% 0.20/0.55  % (27797)------------------------------
% 0.20/0.55  % (27797)------------------------------
% 0.20/0.56  % (27813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (27813)Memory used [KB]: 10874
% 0.20/0.56  % (27813)Time elapsed: 0.141 s
% 0.20/0.56  % (27813)------------------------------
% 0.20/0.56  % (27813)------------------------------
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.56    inference(definition_unfolding,[],[f31,f21])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    ( ! [X20] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f113,f106])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f105,f18])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f104,f17])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f103,f16])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f102,f15])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f99,f32])).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f98])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X2) )),
% 0.20/0.56    inference(superposition,[],[f39,f95])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    ( ! [X0] : (k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f94,f18])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f93,f17])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f92,f16])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f91,f15])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = sK7(sK0,sK1,sK2,sK3,X0,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(resolution,[],[f58,f32])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK5,k2_zfmisc_1(k3_zfmisc_1(X6,X7,X8),X9)) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k1_xboole_0 = X8 | k1_xboole_0 = X9 | sK7(sK0,sK1,sK2,sK3,X5,sK5) = k9_mcart_1(X6,X7,X8,X9,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X5) )),
% 0.20/0.56    inference(superposition,[],[f46,f56])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k3_mcart_1(X5,X6,X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k3_mcart_1(X5,X6,X7),X8)) = X6) )),
% 0.20/0.56    inference(equality_resolution,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k3_mcart_1(X5,X6,X7),X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.20/0.56    inference(definition_unfolding,[],[f23,f21,f20])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.20/0.56    inference(cnf_transformation,[],[f10])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | ~m1_subset_1(X5,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.56    inference(definition_unfolding,[],[f30,f21])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    ( ! [X20] : (~m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f112,f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    sK4 != k9_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    ( ! [X20] : (~m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f111])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ( ! [X20] : (sK5 != sK5 | ~m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK5) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X20) )),
% 0.20/0.56    inference(superposition,[],[f33,f101])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(superposition,[],[f77,f95])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X0] : (sK5 = k4_tarski(k3_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5)),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.20/0.56    inference(superposition,[],[f56,f71])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k3_mcart_1(X6,X7,X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X7) )),
% 0.20/0.56    inference(definition_unfolding,[],[f13,f20])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X7) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f192,plain,(
% 0.20/0.56    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.56    inference(superposition,[],[f19,f129])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (27793)------------------------------
% 0.20/0.56  % (27793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27793)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (27793)Memory used [KB]: 6524
% 0.20/0.56  % (27793)Time elapsed: 0.100 s
% 0.20/0.56  % (27793)------------------------------
% 0.20/0.56  % (27793)------------------------------
% 0.20/0.56  % (27778)Success in time 0.196 s
%------------------------------------------------------------------------------
