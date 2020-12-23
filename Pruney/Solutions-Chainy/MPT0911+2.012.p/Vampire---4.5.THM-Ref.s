%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:30 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 761 expanded)
%              Number of leaves         :   13 ( 167 expanded)
%              Depth                    :   43
%              Number of atoms          :  326 (3437 expanded)
%              Number of equality atoms :  162 (1721 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f482,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f481])).

fof(f481,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f37,f426])).

fof(f426,plain,(
    ! [X0] : k1_xboole_0 = X0 ),
    inference(subsumption_resolution,[],[f425,f269])).

fof(f269,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f239,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f239,plain,(
    ! [X6,X7] : r1_xboole_0(X6,k2_zfmisc_1(k1_xboole_0,X7)) ),
    inference(resolution,[],[f222,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f222,plain,(
    ! [X6,X5] : ~ r2_hidden(X5,k2_zfmisc_1(k1_xboole_0,X6)) ),
    inference(resolution,[],[f201,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f201,plain,(
    ! [X10] : ~ r2_hidden(X10,k1_xboole_0) ),
    inference(backward_demodulation,[],[f170,f182])).

fof(f182,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f174,f40])).

fof(f174,plain,(
    ! [X3] : r1_xboole_0(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f170,f48])).

fof(f170,plain,(
    ! [X10] : ~ r2_hidden(X10,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f169,f102])).

fof(f102,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f101,f76])).

fof(f76,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f34,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f101,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f38,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f63,f52])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f38,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f169,plain,(
    ! [X10] :
      ( sK3 = k2_mcart_1(sK4)
      | ~ r2_hidden(X10,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(superposition,[],[f45,f163])).

fof(f163,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f162,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f162,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3) ),
    inference(subsumption_resolution,[],[f161,f76])).

fof(f161,plain,
    ( sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f153,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f153,plain,
    ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3) ),
    inference(condensation,[],[f152])).

fof(f152,plain,(
    ! [X5] :
      ( sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3)
      | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(superposition,[],[f91,f147])).

fof(f147,plain,(
    ! [X0] :
      ( sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f146,f43])).

fof(f146,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4) ),
    inference(subsumption_resolution,[],[f145,f76])).

fof(f145,plain,
    ( sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f144,f50])).

fof(f144,plain,
    ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( sK4 != X0
      | sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,X0)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,X0)
      | sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f140,f93])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,sK2,X1),k2_zfmisc_1(sK0,sK1))
      | sK3 = sK9(X0,sK2,X1)
      | sK4 != X1
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sK3 = sK9(X0,sK2,X1)
      | ~ r2_hidden(sK8(X0,sK2,X1),k2_zfmisc_1(sK0,sK1))
      | sK4 != X1
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK2))
      | ~ r2_hidden(X1,k2_zfmisc_1(X0,sK2)) ) ),
    inference(resolution,[],[f122,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1,X2),sK2)
      | sK3 = sK9(X0,X1,X2)
      | ~ r2_hidden(sK8(X0,X1,X2),k2_zfmisc_1(sK0,sK1))
      | sK4 != X2
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f119,f91])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK4
      | sK3 = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f118,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | sK3 = X0
      | sK4 != k4_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f115,f93])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X2,sK1,X0),sK0)
      | sK3 = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK1))
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4 ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK4
      | sK3 = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK1))
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(sK8(X2,sK1,X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK1)) ) ),
    inference(resolution,[],[f112,f92])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK9(X2,X3,X1),sK1)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(sK8(X2,X3,X1),sK0) ) ),
    inference(resolution,[],[f109,f49])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK8(X2,X3,X0),sK0)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | sK3 = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK9(X2,X3,X0),sK1) ) ),
    inference(resolution,[],[f103,f49])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK9(X0,X1,X2),sK1)
      | sK4 != k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,sK2)
      | ~ m1_subset_1(sK8(X0,X1,X2),sK0)
      | sK3 = X3
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f77,f91])).

fof(f77,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f425,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) ) ),
    inference(condensation,[],[f424])).

fof(f424,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f423,f269])).

fof(f423,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f422,f36])).

fof(f422,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f419,f35])).

fof(f419,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f87,f388])).

fof(f388,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f380,f40])).

fof(f380,plain,(
    ! [X3] : r1_xboole_0(X3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f376,f48])).

fof(f376,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f371,f37])).

fof(f371,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f363,f40])).

fof(f363,plain,(
    ! [X4,X3] :
      ( r1_xboole_0(X4,sK2)
      | ~ r2_hidden(X3,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f172,f48])).

fof(f172,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X2,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f170,f90])).

fof(f90,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f65,f52])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (16361)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (16353)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (16345)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (16348)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.53  % (16362)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (16341)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (16354)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.54  % (16344)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.54  % (16339)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (16342)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  % (16347)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.54  % (16341)Refutation not found, incomplete strategy% (16341)------------------------------
% 1.42/0.54  % (16341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (16341)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (16341)Memory used [KB]: 10746
% 1.42/0.54  % (16341)Time elapsed: 0.101 s
% 1.42/0.54  % (16341)------------------------------
% 1.42/0.54  % (16341)------------------------------
% 1.42/0.54  % (16347)Refutation not found, incomplete strategy% (16347)------------------------------
% 1.42/0.54  % (16347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (16347)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (16347)Memory used [KB]: 10746
% 1.42/0.54  % (16347)Time elapsed: 0.132 s
% 1.42/0.54  % (16347)------------------------------
% 1.42/0.54  % (16347)------------------------------
% 1.42/0.55  % (16343)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.55  % (16349)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (16340)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.55  % (16357)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (16360)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.55  % (16355)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (16352)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.55  % (16365)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (16368)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.56  % (16359)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.56  % (16366)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.56  % (16346)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.56  % (16364)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.56  % (16358)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.56  % (16367)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (16350)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.56  % (16359)Refutation not found, incomplete strategy% (16359)------------------------------
% 1.42/0.56  % (16359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (16359)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (16359)Memory used [KB]: 10746
% 1.42/0.56  % (16359)Time elapsed: 0.144 s
% 1.42/0.56  % (16359)------------------------------
% 1.42/0.56  % (16359)------------------------------
% 1.42/0.56  % (16363)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.56  % (16349)Refutation not found, incomplete strategy% (16349)------------------------------
% 1.42/0.56  % (16349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (16349)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (16349)Memory used [KB]: 10618
% 1.42/0.56  % (16349)Time elapsed: 0.155 s
% 1.42/0.56  % (16349)------------------------------
% 1.42/0.56  % (16349)------------------------------
% 1.42/0.57  % (16356)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.58  % (16356)Refutation not found, incomplete strategy% (16356)------------------------------
% 1.42/0.58  % (16356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (16356)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (16356)Memory used [KB]: 10618
% 1.42/0.58  % (16356)Time elapsed: 0.165 s
% 1.42/0.58  % (16356)------------------------------
% 1.42/0.58  % (16356)------------------------------
% 1.42/0.59  % (16351)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.59  % (16360)Refutation found. Thanks to Tanya!
% 1.42/0.59  % SZS status Theorem for theBenchmark
% 1.42/0.59  % SZS output start Proof for theBenchmark
% 1.42/0.59  fof(f482,plain,(
% 1.42/0.59    $false),
% 1.42/0.59    inference(trivial_inequality_removal,[],[f481])).
% 1.42/0.59  fof(f481,plain,(
% 1.42/0.59    k1_xboole_0 != k1_xboole_0),
% 1.42/0.59    inference(superposition,[],[f37,f426])).
% 1.42/0.59  fof(f426,plain,(
% 1.42/0.59    ( ! [X0] : (k1_xboole_0 = X0) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f425,f269])).
% 1.42/0.59  fof(f269,plain,(
% 1.42/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.42/0.59    inference(resolution,[],[f239,f40])).
% 1.42/0.59  fof(f40,plain,(
% 1.42/0.59    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.42/0.59    inference(cnf_transformation,[],[f23])).
% 1.42/0.59  fof(f23,plain,(
% 1.42/0.59    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.42/0.59    inference(ennf_transformation,[],[f3])).
% 1.42/0.59  fof(f3,axiom,(
% 1.42/0.59    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.42/0.59  fof(f239,plain,(
% 1.42/0.59    ( ! [X6,X7] : (r1_xboole_0(X6,k2_zfmisc_1(k1_xboole_0,X7))) )),
% 1.42/0.59    inference(resolution,[],[f222,f48])).
% 1.42/0.59  fof(f48,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f24])).
% 1.42/0.59  fof(f24,plain,(
% 1.42/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.59    inference(ennf_transformation,[],[f20])).
% 1.42/0.59  fof(f20,plain,(
% 1.42/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.59    inference(rectify,[],[f2])).
% 1.42/0.60  fof(f2,axiom,(
% 1.42/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.42/0.60  fof(f222,plain,(
% 1.42/0.60    ( ! [X6,X5] : (~r2_hidden(X5,k2_zfmisc_1(k1_xboole_0,X6))) )),
% 1.42/0.60    inference(resolution,[],[f201,f93])).
% 1.42/0.60  fof(f93,plain,(
% 1.42/0.60    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.60    inference(equality_resolution,[],[f57])).
% 1.42/0.60  fof(f57,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.60    inference(cnf_transformation,[],[f4])).
% 1.42/0.60  fof(f4,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.42/0.60  fof(f201,plain,(
% 1.42/0.60    ( ! [X10] : (~r2_hidden(X10,k1_xboole_0)) )),
% 1.42/0.60    inference(backward_demodulation,[],[f170,f182])).
% 1.42/0.60  fof(f182,plain,(
% 1.42/0.60    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.42/0.60    inference(resolution,[],[f174,f40])).
% 1.42/0.60  fof(f174,plain,(
% 1.42/0.60    ( ! [X3] : (r1_xboole_0(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(resolution,[],[f170,f48])).
% 1.42/0.60  fof(f170,plain,(
% 1.42/0.60    ( ! [X10] : (~r2_hidden(X10,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(subsumption_resolution,[],[f169,f102])).
% 1.42/0.60  fof(f102,plain,(
% 1.42/0.60    sK3 != k2_mcart_1(sK4)),
% 1.42/0.60    inference(subsumption_resolution,[],[f101,f76])).
% 1.42/0.60  fof(f76,plain,(
% 1.42/0.60    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.42/0.60    inference(definition_unfolding,[],[f34,f52])).
% 1.42/0.60  fof(f52,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f11])).
% 1.42/0.60  fof(f11,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.42/0.60  fof(f34,plain,(
% 1.42/0.60    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.42/0.60    inference(cnf_transformation,[],[f22])).
% 1.42/0.60  fof(f22,plain,(
% 1.42/0.60    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.42/0.60    inference(flattening,[],[f21])).
% 1.42/0.60  fof(f21,plain,(
% 1.42/0.60    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.42/0.60    inference(ennf_transformation,[],[f19])).
% 1.42/0.60  fof(f19,negated_conjecture,(
% 1.42/0.60    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.42/0.60    inference(negated_conjecture,[],[f18])).
% 1.42/0.60  fof(f18,conjecture,(
% 1.42/0.60    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.42/0.60  fof(f101,plain,(
% 1.42/0.60    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.42/0.60    inference(subsumption_resolution,[],[f100,f35])).
% 1.42/0.60  fof(f35,plain,(
% 1.42/0.60    k1_xboole_0 != sK0),
% 1.42/0.60    inference(cnf_transformation,[],[f22])).
% 1.42/0.60  fof(f100,plain,(
% 1.42/0.60    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 1.42/0.60    inference(subsumption_resolution,[],[f99,f37])).
% 1.42/0.60  fof(f99,plain,(
% 1.42/0.60    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 1.42/0.60    inference(subsumption_resolution,[],[f98,f36])).
% 1.42/0.60  fof(f36,plain,(
% 1.42/0.60    k1_xboole_0 != sK1),
% 1.42/0.60    inference(cnf_transformation,[],[f22])).
% 1.42/0.60  fof(f98,plain,(
% 1.42/0.60    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 1.42/0.60    inference(superposition,[],[f38,f78])).
% 1.42/0.60  fof(f78,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.42/0.60    inference(definition_unfolding,[],[f63,f52])).
% 1.42/0.60  fof(f63,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f28])).
% 1.42/0.60  fof(f28,plain,(
% 1.42/0.60    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.42/0.60    inference(ennf_transformation,[],[f15])).
% 1.42/0.60  fof(f15,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.42/0.60  fof(f38,plain,(
% 1.42/0.60    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.42/0.60    inference(cnf_transformation,[],[f22])).
% 1.42/0.60  fof(f169,plain,(
% 1.42/0.60    ( ! [X10] : (sK3 = k2_mcart_1(sK4) | ~r2_hidden(X10,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(superposition,[],[f45,f163])).
% 1.42/0.60  fof(f163,plain,(
% 1.42/0.60    ( ! [X0] : (sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(resolution,[],[f162,f43])).
% 1.42/0.60  fof(f43,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f1])).
% 1.42/0.60  fof(f1,axiom,(
% 1.42/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.42/0.60  fof(f162,plain,(
% 1.42/0.60    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3)),
% 1.42/0.60    inference(subsumption_resolution,[],[f161,f76])).
% 1.42/0.60  fof(f161,plain,(
% 1.42/0.60    sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.42/0.60    inference(resolution,[],[f153,f50])).
% 1.42/0.60  fof(f50,plain,(
% 1.42/0.60    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f27])).
% 1.42/0.60  fof(f27,plain,(
% 1.42/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.42/0.60    inference(flattening,[],[f26])).
% 1.42/0.60  fof(f26,plain,(
% 1.42/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.42/0.60    inference(ennf_transformation,[],[f9])).
% 1.42/0.60  fof(f9,axiom,(
% 1.42/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.42/0.60  fof(f153,plain,(
% 1.42/0.60    ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3)),
% 1.42/0.60    inference(condensation,[],[f152])).
% 1.42/0.60  fof(f152,plain,(
% 1.42/0.60    ( ! [X5] : (sK4 = k4_tarski(sK8(k2_zfmisc_1(sK0,sK1),sK2,sK4),sK3) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(X5,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(superposition,[],[f91,f147])).
% 1.42/0.60  fof(f147,plain,(
% 1.42/0.60    ( ! [X0] : (sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(resolution,[],[f146,f43])).
% 1.42/0.60  fof(f146,plain,(
% 1.42/0.60    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4)),
% 1.42/0.60    inference(subsumption_resolution,[],[f145,f76])).
% 1.42/0.60  fof(f145,plain,(
% 1.42/0.60    sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.42/0.60    inference(resolution,[],[f144,f50])).
% 1.42/0.60  fof(f144,plain,(
% 1.42/0.60    ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,sK4)),
% 1.42/0.60    inference(equality_resolution,[],[f143])).
% 1.42/0.60  fof(f143,plain,(
% 1.42/0.60    ( ! [X0] : (sK4 != X0 | sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,X0) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(duplicate_literal_removal,[],[f141])).
% 1.42/0.60  fof(f141,plain,(
% 1.42/0.60    ( ! [X0] : (sK3 = sK9(k2_zfmisc_1(sK0,sK1),sK2,X0) | sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.42/0.60    inference(resolution,[],[f140,f93])).
% 1.42/0.60  fof(f140,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~r2_hidden(sK8(X0,sK2,X1),k2_zfmisc_1(sK0,sK1)) | sK3 = sK9(X0,sK2,X1) | sK4 != X1 | ~r2_hidden(X1,k2_zfmisc_1(X0,sK2))) )),
% 1.42/0.60    inference(duplicate_literal_removal,[],[f138])).
% 1.42/0.60  fof(f138,plain,(
% 1.42/0.60    ( ! [X0,X1] : (sK3 = sK9(X0,sK2,X1) | ~r2_hidden(sK8(X0,sK2,X1),k2_zfmisc_1(sK0,sK1)) | sK4 != X1 | ~r2_hidden(X1,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(X1,k2_zfmisc_1(X0,sK2))) )),
% 1.42/0.60    inference(resolution,[],[f122,f92])).
% 1.42/0.60  fof(f92,plain,(
% 1.42/0.60    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.60    inference(equality_resolution,[],[f58])).
% 1.42/0.60  fof(f58,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.60    inference(cnf_transformation,[],[f4])).
% 1.42/0.60  fof(f122,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK9(X0,X1,X2),sK2) | sK3 = sK9(X0,X1,X2) | ~r2_hidden(sK8(X0,X1,X2),k2_zfmisc_1(sK0,sK1)) | sK4 != X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.60    inference(superposition,[],[f119,f91])).
% 1.42/0.60  fof(f119,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK4 | sK3 = X1 | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK2)) )),
% 1.42/0.60    inference(resolution,[],[f118,f49])).
% 1.42/0.60  fof(f49,plain,(
% 1.42/0.60    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f25])).
% 1.42/0.60  fof(f25,plain,(
% 1.42/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.42/0.60    inference(ennf_transformation,[],[f8])).
% 1.42/0.60  fof(f8,axiom,(
% 1.42/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.42/0.60  fof(f118,plain,(
% 1.42/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | ~r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | sK3 = X0 | sK4 != k4_tarski(X1,X0)) )),
% 1.42/0.60    inference(duplicate_literal_removal,[],[f116])).
% 1.42/0.60  fof(f116,plain,(
% 1.42/0.60    ( ! [X0,X1] : (sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | ~r2_hidden(X1,k2_zfmisc_1(sK0,sK1))) )),
% 1.42/0.60    inference(resolution,[],[f115,f93])).
% 1.42/0.60  fof(f115,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK8(X2,sK1,X0),sK0) | sK3 = X1 | ~r2_hidden(X0,k2_zfmisc_1(X2,sK1)) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4) )),
% 1.42/0.60    inference(duplicate_literal_removal,[],[f113])).
% 1.42/0.60  fof(f113,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK4 | sK3 = X1 | ~r2_hidden(X0,k2_zfmisc_1(X2,sK1)) | ~m1_subset_1(X1,sK2) | ~r2_hidden(sK8(X2,sK1,X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK1))) )),
% 1.42/0.60    inference(resolution,[],[f112,f92])).
% 1.42/0.60  fof(f112,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK9(X2,X3,X1),sK1) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | ~m1_subset_1(X0,sK2) | ~r2_hidden(sK8(X2,X3,X1),sK0)) )),
% 1.42/0.60    inference(resolution,[],[f109,f49])).
% 1.42/0.60  fof(f109,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK8(X2,X3,X0),sK0) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | sK3 = X1 | ~r2_hidden(X0,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK9(X2,X3,X0),sK1)) )),
% 1.42/0.60    inference(resolution,[],[f103,f49])).
% 1.42/0.60  fof(f103,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK9(X0,X1,X2),sK1) | sK4 != k4_tarski(X2,X3) | ~m1_subset_1(X3,sK2) | ~m1_subset_1(sK8(X0,X1,X2),sK0) | sK3 = X3 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.60    inference(superposition,[],[f77,f91])).
% 1.42/0.60  fof(f77,plain,(
% 1.42/0.60    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 1.42/0.60    inference(definition_unfolding,[],[f33,f51])).
% 1.42/0.60  fof(f51,plain,(
% 1.42/0.60    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.42/0.60    inference(cnf_transformation,[],[f10])).
% 1.42/0.60  fof(f10,axiom,(
% 1.42/0.60    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.42/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.42/0.60  fof(f33,plain,(
% 1.42/0.60    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 1.42/0.60    inference(cnf_transformation,[],[f22])).
% 1.42/0.60  fof(f91,plain,(
% 1.42/0.60    ( ! [X0,X3,X1] : (k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3 | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.60    inference(equality_resolution,[],[f59])).
% 1.42/0.60  fof(f59,plain,(
% 1.42/0.60    ( ! [X2,X0,X3,X1] : (k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.60    inference(cnf_transformation,[],[f4])).
% 1.42/0.60  fof(f45,plain,(
% 1.42/0.60    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.42/0.60    inference(cnf_transformation,[],[f17])).
% 1.42/0.61  fof(f17,axiom,(
% 1.42/0.61    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.42/0.61  fof(f425,plain,(
% 1.42/0.61    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.42/0.61    inference(condensation,[],[f424])).
% 1.42/0.61  fof(f424,plain,(
% 1.42/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.42/0.61    inference(forward_demodulation,[],[f423,f269])).
% 1.42/0.61  fof(f423,plain,(
% 1.42/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.42/0.61    inference(subsumption_resolution,[],[f422,f36])).
% 1.42/0.61  fof(f422,plain,(
% 1.42/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) | k1_xboole_0 = sK1 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.42/0.61    inference(subsumption_resolution,[],[f419,f35])).
% 1.42/0.61  fof(f419,plain,(
% 1.42/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.42/0.61    inference(superposition,[],[f87,f388])).
% 1.42/0.61  fof(f388,plain,(
% 1.42/0.61    k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.42/0.61    inference(resolution,[],[f380,f40])).
% 1.42/0.61  fof(f380,plain,(
% 1.42/0.61    ( ! [X3] : (r1_xboole_0(X3,k2_zfmisc_1(sK0,sK1))) )),
% 1.42/0.61    inference(resolution,[],[f376,f48])).
% 1.42/0.61  fof(f376,plain,(
% 1.42/0.61    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) )),
% 1.42/0.61    inference(subsumption_resolution,[],[f371,f37])).
% 1.42/0.61  fof(f371,plain,(
% 1.42/0.61    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK2) )),
% 1.42/0.61    inference(resolution,[],[f363,f40])).
% 1.42/0.61  fof(f363,plain,(
% 1.42/0.61    ( ! [X4,X3] : (r1_xboole_0(X4,sK2) | ~r2_hidden(X3,k2_zfmisc_1(sK0,sK1))) )),
% 1.42/0.61    inference(resolution,[],[f172,f48])).
% 1.42/0.61  fof(f172,plain,(
% 1.42/0.61    ( ! [X2,X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X2,k2_zfmisc_1(sK0,sK1))) )),
% 1.42/0.61    inference(resolution,[],[f170,f90])).
% 1.42/0.61  fof(f90,plain,(
% 1.42/0.61    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.42/0.61    inference(equality_resolution,[],[f89])).
% 1.42/0.61  fof(f89,plain,(
% 1.42/0.61    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.61    inference(equality_resolution,[],[f60])).
% 1.42/0.61  fof(f60,plain,(
% 1.42/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.61    inference(cnf_transformation,[],[f4])).
% 1.42/0.61  fof(f87,plain,(
% 1.42/0.61    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.42/0.61    inference(definition_unfolding,[],[f70,f75])).
% 1.42/0.61  fof(f75,plain,(
% 1.42/0.61    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.42/0.61    inference(definition_unfolding,[],[f65,f52])).
% 1.42/0.61  fof(f65,plain,(
% 1.42/0.61    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.42/0.61    inference(cnf_transformation,[],[f12])).
% 1.42/0.61  fof(f12,axiom,(
% 1.42/0.61    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.42/0.61  fof(f70,plain,(
% 1.42/0.61    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.42/0.61    inference(cnf_transformation,[],[f16])).
% 1.42/0.61  fof(f16,axiom,(
% 1.42/0.61    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.42/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.42/0.61  fof(f37,plain,(
% 1.42/0.61    k1_xboole_0 != sK2),
% 1.42/0.61    inference(cnf_transformation,[],[f22])).
% 1.42/0.61  % SZS output end Proof for theBenchmark
% 1.42/0.61  % (16360)------------------------------
% 1.42/0.61  % (16360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.61  % (16360)Termination reason: Refutation
% 1.42/0.61  
% 1.42/0.61  % (16360)Memory used [KB]: 1918
% 1.42/0.61  % (16360)Time elapsed: 0.181 s
% 1.42/0.61  % (16360)------------------------------
% 1.42/0.61  % (16360)------------------------------
% 1.42/0.61  % (16338)Success in time 0.247 s
%------------------------------------------------------------------------------
