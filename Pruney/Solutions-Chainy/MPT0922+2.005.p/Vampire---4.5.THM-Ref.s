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
% DateTime   : Thu Dec  3 12:59:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   93 (1865 expanded)
%              Number of leaves         :    6 ( 397 expanded)
%              Depth                    :   28
%              Number of atoms          :  440 (12781 expanded)
%              Number of equality atoms :  331 (8113 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f201])).

fof(f201,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f133,f133])).

fof(f133,plain,(
    ! [X0] : k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ),
    inference(subsumption_resolution,[],[f132,f21])).

fof(f21,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

% (20212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
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
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
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
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

fof(f132,plain,(
    ! [X0] :
      ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f131,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f130,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f130,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f129,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f129,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(subsumption_resolution,[],[f128,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f128,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(resolution,[],[f126,f39])).

fof(f39,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f16,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f126,plain,(
    ! [X19,X17,X15,X18,X16] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18),X19))
      | k1_xboole_0 = X16
      | k1_xboole_0 = X17
      | k1_xboole_0 = X18
      | k1_xboole_0 = X19
      | sK4 = k11_mcart_1(X16,X17,X18,X19,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X15 ) ),
    inference(superposition,[],[f54,f122])).

fof(f122,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(superposition,[],[f108,f118])).

fof(f118,plain,(
    ! [X20] :
      ( sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20 ) ),
    inference(subsumption_resolution,[],[f117,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f83,f73])).

fof(f73,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f72,f17])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f71,f20])).

fof(f71,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f70,f19])).

fof(f70,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(subsumption_resolution,[],[f69,f18])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f82,f20])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f81,f19])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f18])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f17])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X5
                      & m1_subset_1(X9,X3) )
                  & m1_subset_1(X8,X2) )
              & m1_subset_1(X7,X1) )
          & m1_subset_1(X6,X0) )
      | ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ? [X9] :
                      ( X4 != X7
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
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f117,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20 ) ),
    inference(subsumption_resolution,[],[f116,f102])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f101,f73])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f99,f19])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f98,f18])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f97,f17])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20 ) ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f95,f73])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f20])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f92,f18])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f17])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f115,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20 ) ),
    inference(subsumption_resolution,[],[f114,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f89,f73])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f88,f20])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f19])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f18])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f17])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20 ) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,(
    ! [X20] :
      ( sK5 != sK5
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1)
      | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2)
      | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0)
      | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20 ) ),
    inference(superposition,[],[f15,f108])).

fof(f15,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X9 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 ) ),
    inference(forward_demodulation,[],[f107,f73])).

fof(f107,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f106,f20])).

fof(f106,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f19])).

fof(f105,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f104,f18])).

fof(f104,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f103,f17])).

fof(f103,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k9_mcart_1(X0,X1,X2,X3,X5) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 ) ),
    inference(equality_resolution,[],[f44])).

% (20215)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f4])).

% (20197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
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

fof(f206,plain,(
    sK4 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(superposition,[],[f21,f133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (20196)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (20205)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (20196)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 1.31/0.56  % (20205)Refutation not found, incomplete strategy% (20205)------------------------------
% 1.31/0.56  % (20205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (20205)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (20205)Memory used [KB]: 6140
% 1.31/0.56  % (20205)Time elapsed: 0.003 s
% 1.31/0.56  % (20205)------------------------------
% 1.31/0.56  % (20205)------------------------------
% 1.31/0.56  % SZS output start Proof for theBenchmark
% 1.31/0.56  fof(f208,plain,(
% 1.31/0.56    $false),
% 1.31/0.56    inference(subsumption_resolution,[],[f206,f201])).
% 1.31/0.56  fof(f201,plain,(
% 1.31/0.56    ( ! [X0,X1] : (X0 = X1) )),
% 1.31/0.56    inference(superposition,[],[f133,f133])).
% 1.31/0.56  fof(f133,plain,(
% 1.31/0.56    ( ! [X0] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f132,f21])).
% 1.31/0.56  fof(f21,plain,(
% 1.31/0.56    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f9,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3,X4,X5] : (k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.56    inference(flattening,[],[f8])).
% 1.31/0.56  fof(f8,plain,(
% 1.31/0.56    ? [X0,X1,X2,X3,X4,X5] : (((k11_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X9 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.56    inference(ennf_transformation,[],[f7])).
% 1.31/0.56  % (20212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.56  fof(f7,negated_conjecture,(
% 1.31/0.56    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.31/0.56    inference(negated_conjecture,[],[f6])).
% 1.31/0.56  fof(f6,conjecture,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X9))))) => (k11_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).
% 1.31/0.56  fof(f132,plain,(
% 1.31/0.56    ( ! [X0] : (sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f131,f20])).
% 1.31/0.56  fof(f20,plain,(
% 1.31/0.56    k1_xboole_0 != sK3),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f131,plain,(
% 1.31/0.56    ( ! [X0] : (k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f130,f19])).
% 1.31/0.56  fof(f19,plain,(
% 1.31/0.56    k1_xboole_0 != sK2),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f130,plain,(
% 1.31/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f129,f18])).
% 1.31/0.56  fof(f18,plain,(
% 1.31/0.56    k1_xboole_0 != sK1),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f129,plain,(
% 1.31/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f128,f17])).
% 1.31/0.56  fof(f17,plain,(
% 1.31/0.56    k1_xboole_0 != sK0),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f128,plain,(
% 1.31/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(resolution,[],[f126,f39])).
% 1.31/0.56  fof(f39,plain,(
% 1.31/0.56    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.31/0.56    inference(definition_unfolding,[],[f16,f38])).
% 1.31/0.56  fof(f38,plain,(
% 1.31/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.31/0.56    inference(definition_unfolding,[],[f23,f22])).
% 1.31/0.56  fof(f22,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f1])).
% 1.31/0.56  fof(f1,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.31/0.56  fof(f23,plain,(
% 1.31/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f2])).
% 1.31/0.56  fof(f2,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.31/0.56  fof(f16,plain,(
% 1.31/0.56    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f126,plain,(
% 1.31/0.56    ( ! [X19,X17,X15,X18,X16] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18),X19)) | k1_xboole_0 = X16 | k1_xboole_0 = X17 | k1_xboole_0 = X18 | k1_xboole_0 = X19 | sK4 = k11_mcart_1(X16,X17,X18,X19,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X15) )),
% 1.31/0.56    inference(superposition,[],[f54,f122])).
% 1.31/0.56  fof(f122,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(duplicate_literal_removal,[],[f119])).
% 1.31/0.56  fof(f119,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK4) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0 | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(superposition,[],[f108,f118])).
% 1.31/0.56  fof(f118,plain,(
% 1.31/0.56    ( ! [X20] : (sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f117,f84])).
% 1.31/0.56  fof(f84,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(forward_demodulation,[],[f83,f73])).
% 1.31/0.56  fof(f73,plain,(
% 1.31/0.56    k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 1.31/0.56    inference(subsumption_resolution,[],[f72,f17])).
% 1.31/0.56  fof(f72,plain,(
% 1.31/0.56    k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 1.31/0.56    inference(subsumption_resolution,[],[f71,f20])).
% 1.31/0.56  fof(f71,plain,(
% 1.31/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 1.31/0.56    inference(subsumption_resolution,[],[f70,f19])).
% 1.31/0.56  fof(f70,plain,(
% 1.31/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 1.31/0.56    inference(subsumption_resolution,[],[f69,f18])).
% 1.31/0.56  fof(f69,plain,(
% 1.31/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 1.31/0.56    inference(resolution,[],[f42,f39])).
% 1.31/0.56  fof(f42,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.31/0.56    inference(definition_unfolding,[],[f25,f38])).
% 1.31/0.56  fof(f25,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f10])).
% 1.31/0.56  fof(f10,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.31/0.56    inference(ennf_transformation,[],[f3])).
% 1.31/0.56  fof(f3,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.31/0.56  fof(f83,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f82,f20])).
% 1.31/0.56  fof(f82,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f81,f19])).
% 1.31/0.56  fof(f81,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f80,f18])).
% 1.31/0.56  fof(f80,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f79,f17])).
% 1.31/0.56  fof(f79,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(resolution,[],[f48,f39])).
% 1.31/0.56  fof(f48,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(definition_unfolding,[],[f37,f38])).
% 1.31/0.56  fof(f37,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4,X5),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  fof(f14,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X6] : (? [X7] : (? [X8] : (? [X9] : (X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5 & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0)) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.56    inference(flattening,[],[f13])).
% 1.31/0.56  fof(f13,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X6] : (? [X7] : (? [X8] : (? [X9] : ((X4 != X7 & k4_mcart_1(X6,X7,X8,X9) = X5) & m1_subset_1(X9,X3)) & m1_subset_1(X8,X2)) & m1_subset_1(X7,X1)) & m1_subset_1(X6,X0))) | ~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.56    inference(ennf_transformation,[],[f5])).
% 1.31/0.56  fof(f5,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).
% 1.31/0.56  fof(f117,plain,(
% 1.31/0.56    ( ! [X20] : (~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f116,f102])).
% 1.31/0.56  fof(f102,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(forward_demodulation,[],[f101,f73])).
% 1.31/0.56  fof(f101,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f100,f20])).
% 1.31/0.56  fof(f100,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f99,f19])).
% 1.31/0.56  fof(f99,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f98,f18])).
% 1.31/0.56  fof(f98,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f97,f17])).
% 1.31/0.56  fof(f97,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK9(sK0,sK1,sK2,sK3,X0,sK5),sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(resolution,[],[f53,f39])).
% 1.31/0.56  fof(f53,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(definition_unfolding,[],[f32,f38])).
% 1.31/0.56  fof(f32,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4,X5),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  fof(f116,plain,(
% 1.31/0.56    ( ! [X20] : (~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f115,f96])).
% 1.31/0.56  fof(f96,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(forward_demodulation,[],[f95,f73])).
% 1.31/0.56  fof(f95,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f94,f20])).
% 1.31/0.56  fof(f94,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f93,f19])).
% 1.31/0.56  fof(f93,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f92,f18])).
% 1.31/0.56  fof(f92,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f91,f17])).
% 1.31/0.56  fof(f91,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK8(sK0,sK1,sK2,sK3,X0,sK5),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(resolution,[],[f50,f39])).
% 1.31/0.56  fof(f50,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(definition_unfolding,[],[f35,f38])).
% 1.31/0.56  fof(f35,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  fof(f115,plain,(
% 1.31/0.56    ( ! [X20] : (~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f114,f90])).
% 1.31/0.56  fof(f90,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(forward_demodulation,[],[f89,f73])).
% 1.31/0.56  fof(f89,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f88,f20])).
% 1.31/0.56  fof(f88,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f87,f19])).
% 1.31/0.56  fof(f87,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f86,f18])).
% 1.31/0.56  fof(f86,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f85,f17])).
% 1.31/0.56  fof(f85,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,sK3,X0,sK5),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(resolution,[],[f49,f39])).
% 1.31/0.56  fof(f49,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(definition_unfolding,[],[f36,f38])).
% 1.31/0.56  fof(f36,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4,X5),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  fof(f114,plain,(
% 1.31/0.56    ( ! [X20] : (~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20) )),
% 1.31/0.56    inference(trivial_inequality_removal,[],[f113])).
% 1.31/0.56  fof(f113,plain,(
% 1.31/0.56    ( ! [X20] : (sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,X20,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,X20,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,X20,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,X20,sK5),sK0) | sK4 = sK9(sK0,sK1,sK2,sK3,X20,sK5) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X20) )),
% 1.31/0.56    inference(superposition,[],[f15,f108])).
% 1.31/0.56  fof(f15,plain,(
% 1.31/0.56    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X9) )),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f108,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) = X0) )),
% 1.31/0.56    inference(forward_demodulation,[],[f107,f73])).
% 1.31/0.56  fof(f107,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f106,f20])).
% 1.31/0.56  fof(f106,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f105,f19])).
% 1.31/0.56  fof(f105,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f104,f18])).
% 1.31/0.56  fof(f104,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(subsumption_resolution,[],[f103,f17])).
% 1.31/0.56  fof(f103,plain,(
% 1.31/0.56    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,X0,sK5),sK7(sK0,sK1,sK2,sK3,X0,sK5),sK8(sK0,sK1,sK2,sK3,X0,sK5),sK9(sK0,sK1,sK2,sK3,X0,sK5)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 1.31/0.56    inference(resolution,[],[f52,f39])).
% 1.31/0.56  fof(f52,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(definition_unfolding,[],[f33,f38])).
% 1.31/0.56  fof(f33,plain,(
% 1.31/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4,X5),sK7(X0,X1,X2,X3,X4,X5),sK8(X0,X1,X2,X3,X4,X5),sK9(X0,X1,X2,X3,X4,X5)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k9_mcart_1(X0,X1,X2,X3,X5) = X4) )),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  fof(f54,plain,(
% 1.31/0.56    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8) )),
% 1.31/0.56    inference(equality_resolution,[],[f44])).
% 1.31/0.56  % (20215)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.56  fof(f44,plain,(
% 1.31/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 1.31/0.56    inference(definition_unfolding,[],[f31,f38])).
% 1.31/0.56  fof(f31,plain,(
% 1.31/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 1.31/0.56    inference(cnf_transformation,[],[f12])).
% 1.31/0.56  fof(f12,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.56    inference(flattening,[],[f11])).
% 1.31/0.56  fof(f11,plain,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.56    inference(ennf_transformation,[],[f4])).
% 1.31/0.56  % (20197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.56  fof(f4,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 1.31/0.56  fof(f206,plain,(
% 1.31/0.56    sK4 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))),
% 1.31/0.56    inference(superposition,[],[f21,f133])).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (20196)------------------------------
% 1.31/0.56  % (20196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (20196)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (20196)Memory used [KB]: 6396
% 1.31/0.56  % (20196)Time elapsed: 0.120 s
% 1.31/0.56  % (20196)------------------------------
% 1.31/0.56  % (20196)------------------------------
% 1.31/0.56  % (20189)Success in time 0.199 s
%------------------------------------------------------------------------------
