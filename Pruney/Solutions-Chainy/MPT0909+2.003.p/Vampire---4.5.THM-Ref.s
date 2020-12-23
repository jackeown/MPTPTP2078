%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:23 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 543 expanded)
%              Number of leaves         :   13 ( 124 expanded)
%              Depth                    :   37
%              Number of atoms          :  314 (2362 expanded)
%              Number of equality atoms :  156 (1139 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f337,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f336])).

fof(f336,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f36,f278])).

fof(f278,plain,(
    ! [X2] : k1_xboole_0 = X2 ),
    inference(subsumption_resolution,[],[f201,f216])).

fof(f216,plain,(
    ! [X6] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f213,f192])).

fof(f192,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f104,f178])).

fof(f178,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f171,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(resolution,[],[f160,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f160,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f155,f112])).

fof(f112,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f77,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f77,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f33,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f155,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X5))
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(resolution,[],[f145,f44])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2)) ) ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f136,f41])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f135,f112])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f133,f41])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X1,sK2))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ) ),
    inference(resolution,[],[f132,f112])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f131,f113])).

fof(f113,plain,(
    sK3 != k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f111,f77])).

fof(f111,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f110,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f108,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f108,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f37,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f54])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f37,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( sK3 = k1_mcart_1(k1_mcart_1(sK4))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK4 != X0
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4)) ) ),
    inference(resolution,[],[f128,f55])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK2))
      | sK4 != X0 ) ),
    inference(condensation,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f125,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | sK4 != X0 ) ),
    inference(resolution,[],[f124,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,X3)
      | sK4 != X0 ) ),
    inference(superposition,[],[f122,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != sK4
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X3)) ) ),
    inference(resolution,[],[f121,f55])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),sK0)
      | sK4 != k4_tarski(X0,X2)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(condensation,[],[f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sK4 != k4_tarski(X0,X3)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X4,sK1)) ) ),
    inference(resolution,[],[f118,f56])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sK4 != k4_tarski(X0,X3)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f117,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3))
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(k2_mcart_1(X0),sK1)
      | ~ r2_hidden(k1_mcart_1(X0),sK0) ) ),
    inference(resolution,[],[f116,f45])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = k1_mcart_1(X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f115,f49])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X0),sK1) ) ),
    inference(resolution,[],[f114,f49])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f78,f47])).

fof(f78,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X5 ) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X5 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f213,plain,(
    ! [X6] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X6) ),
    inference(superposition,[],[f105,f192])).

fof(f105,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f201,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f200,f36])).

fof(f200,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f199,f35])).

fof(f199,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f191,f34])).

fof(f191,plain,(
    ! [X2] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f96,f178])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f69,f76])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (12099)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (12091)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (12080)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12079)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (12083)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12083)Refutation not found, incomplete strategy% (12083)------------------------------
% 0.20/0.54  % (12083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12076)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (12075)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (12091)Refutation not found, incomplete strategy% (12091)------------------------------
% 0.20/0.54  % (12091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12091)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12091)Memory used [KB]: 10618
% 0.20/0.54  % (12091)Time elapsed: 0.123 s
% 0.20/0.54  % (12091)------------------------------
% 0.20/0.54  % (12091)------------------------------
% 0.20/0.54  % (12083)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12083)Memory used [KB]: 10746
% 0.20/0.54  % (12083)Time elapsed: 0.128 s
% 0.20/0.54  % (12083)------------------------------
% 0.20/0.54  % (12083)------------------------------
% 0.20/0.54  % (12076)Refutation not found, incomplete strategy% (12076)------------------------------
% 0.20/0.54  % (12076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12076)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12076)Memory used [KB]: 10746
% 0.20/0.54  % (12076)Time elapsed: 0.123 s
% 0.20/0.54  % (12076)------------------------------
% 0.20/0.54  % (12076)------------------------------
% 0.20/0.54  % (12097)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (12098)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (12097)Refutation not found, incomplete strategy% (12097)------------------------------
% 0.20/0.54  % (12097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12097)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12097)Memory used [KB]: 1791
% 0.20/0.54  % (12097)Time elapsed: 0.087 s
% 0.20/0.54  % (12097)------------------------------
% 0.20/0.54  % (12097)------------------------------
% 0.20/0.54  % (12103)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (12077)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (12102)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (12089)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (12078)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (12100)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (12092)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (12081)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (12093)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (12095)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (12096)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (12094)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (12096)Refutation not found, incomplete strategy% (12096)------------------------------
% 0.20/0.56  % (12096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (12096)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (12096)Memory used [KB]: 10874
% 0.20/0.56  % (12096)Time elapsed: 0.148 s
% 0.20/0.56  % (12096)------------------------------
% 0.20/0.56  % (12096)------------------------------
% 0.20/0.56  % (12085)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (12084)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (12084)Refutation not found, incomplete strategy% (12084)------------------------------
% 0.20/0.56  % (12084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (12084)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (12084)Memory used [KB]: 10618
% 0.20/0.56  % (12084)Time elapsed: 0.147 s
% 0.20/0.56  % (12084)------------------------------
% 0.20/0.56  % (12084)------------------------------
% 0.20/0.56  % (12088)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (12087)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (12086)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (12101)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (12074)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.58  % (12074)Refutation not found, incomplete strategy% (12074)------------------------------
% 1.62/0.58  % (12074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (12095)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f337,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f336])).
% 1.62/0.58  fof(f336,plain,(
% 1.62/0.58    k1_xboole_0 != k1_xboole_0),
% 1.62/0.58    inference(superposition,[],[f36,f278])).
% 1.62/0.58  fof(f278,plain,(
% 1.62/0.58    ( ! [X2] : (k1_xboole_0 = X2) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f201,f216])).
% 1.62/0.58  fof(f216,plain,(
% 1.62/0.58    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X6)) )),
% 1.62/0.58    inference(forward_demodulation,[],[f213,f192])).
% 1.62/0.58  fof(f192,plain,(
% 1.62/0.58    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.62/0.58    inference(superposition,[],[f104,f178])).
% 1.62/0.58  fof(f178,plain,(
% 1.62/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f174])).
% 1.62/0.58  fof(f174,plain,(
% 1.62/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.62/0.58    inference(resolution,[],[f171,f44])).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f23])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.62/0.58    inference(ennf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,axiom,(
% 1.62/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.62/0.58  fof(f171,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 1.62/0.58    inference(resolution,[],[f160,f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.62/0.58  fof(f160,plain,(
% 1.62/0.58    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.62/0.58    inference(resolution,[],[f155,f112])).
% 1.62/0.58  fof(f112,plain,(
% 1.62/0.58    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.62/0.58    inference(resolution,[],[f77,f48])).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.62/0.58    inference(flattening,[],[f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.62/0.58  fof(f77,plain,(
% 1.62/0.58    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.62/0.58    inference(definition_unfolding,[],[f33,f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.62/0.58    inference(cnf_transformation,[],[f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.62/0.58    inference(flattening,[],[f21])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.62/0.58    inference(ennf_transformation,[],[f20])).
% 1.62/0.58  fof(f20,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.62/0.58    inference(negated_conjecture,[],[f19])).
% 1.62/0.58  fof(f19,conjecture,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 1.62/0.58  fof(f155,plain,(
% 1.62/0.58    ( ! [X4,X5] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X5)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 1.62/0.58    inference(resolution,[],[f145,f44])).
% 1.62/0.58  fof(f145,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X1,sK1),X2))) )),
% 1.62/0.58    inference(resolution,[],[f141,f55])).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.62/0.58    inference(ennf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.62/0.58  fof(f141,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f136,f41])).
% 1.62/0.58  fof(f136,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.62/0.58    inference(resolution,[],[f135,f112])).
% 1.62/0.58  fof(f135,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 1.62/0.58    inference(resolution,[],[f133,f41])).
% 1.62/0.58  fof(f133,plain,(
% 1.62/0.58    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(sK4,k2_zfmisc_1(X1,sK2)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) )),
% 1.62/0.58    inference(resolution,[],[f132,f112])).
% 1.62/0.58  fof(f132,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(sK4,k2_zfmisc_1(X0,sK2))) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f131,f113])).
% 1.62/0.58  fof(f113,plain,(
% 1.62/0.58    sK3 != k1_mcart_1(k1_mcart_1(sK4))),
% 1.62/0.58    inference(subsumption_resolution,[],[f111,f77])).
% 1.62/0.58  fof(f111,plain,(
% 1.62/0.58    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.62/0.58    inference(subsumption_resolution,[],[f110,f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    k1_xboole_0 != sK0),
% 1.62/0.58    inference(cnf_transformation,[],[f22])).
% 1.62/0.58  fof(f110,plain,(
% 1.62/0.58    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 1.62/0.58    inference(subsumption_resolution,[],[f109,f36])).
% 1.62/0.58  fof(f109,plain,(
% 1.62/0.58    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 1.62/0.58    inference(subsumption_resolution,[],[f108,f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    k1_xboole_0 != sK1),
% 1.62/0.58    inference(cnf_transformation,[],[f22])).
% 1.62/0.58  fof(f108,plain,(
% 1.62/0.58    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 1.62/0.58    inference(superposition,[],[f37,f83])).
% 1.62/0.58  fof(f83,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.62/0.58    inference(definition_unfolding,[],[f57,f54])).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.62/0.58    inference(ennf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 1.62/0.58    inference(cnf_transformation,[],[f22])).
% 1.62/0.58  fof(f131,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~r2_hidden(sK4,k2_zfmisc_1(X0,sK2)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))) )),
% 1.62/0.58    inference(equality_resolution,[],[f129])).
% 1.62/0.58  fof(f129,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (sK4 != X0 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK2)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X3),X4))) )),
% 1.62/0.58    inference(resolution,[],[f128,f55])).
% 1.62/0.58  fof(f128,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(X1,sK2)) | sK4 != X0) )),
% 1.62/0.58    inference(condensation,[],[f126])).
% 1.62/0.58  fof(f126,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 1.62/0.58    inference(resolution,[],[f125,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f125,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | sK4 != X0) )),
% 1.62/0.58    inference(resolution,[],[f124,f45])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.62/0.58  fof(f124,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,X3) | sK4 != X0) )),
% 1.62/0.58    inference(superposition,[],[f122,f47])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f24])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,axiom,(
% 1.62/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.62/0.58  fof(f122,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != sK4 | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X2,sK1)) | ~r2_hidden(X1,sK2) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X3))) )),
% 1.62/0.58    inference(resolution,[],[f121,f55])).
% 1.62/0.58  fof(f121,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k1_mcart_1(X0),sK0) | sK4 != k4_tarski(X0,X2) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X1,sK1)) | ~r2_hidden(X2,sK2)) )),
% 1.62/0.58    inference(condensation,[],[f119])).
% 1.62/0.58  fof(f119,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sK4 != k4_tarski(X0,X3) | k1_mcart_1(X0) = sK3 | ~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X4,sK1))) )),
% 1.62/0.58    inference(resolution,[],[f118,f56])).
% 1.62/0.58  fof(f118,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sK4 != k4_tarski(X0,X3) | k1_mcart_1(X0) = sK3 | ~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X3,sK2)) )),
% 1.62/0.58    inference(resolution,[],[f117,f49])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.62/0.58  fof(f117,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,sK2) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X2,X3)) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(k2_mcart_1(X0),sK1) | ~r2_hidden(k1_mcart_1(X0),sK0)) )),
% 1.62/0.58    inference(resolution,[],[f116,f45])).
% 1.62/0.58  fof(f116,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | sK4 != k4_tarski(X1,X0) | sK3 = k1_mcart_1(X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X0,sK2) | ~r2_hidden(k2_mcart_1(X1),sK1) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 1.62/0.58    inference(resolution,[],[f115,f49])).
% 1.62/0.58  fof(f115,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(X0),sK0) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X0),sK1)) )),
% 1.62/0.58    inference(resolution,[],[f114,f49])).
% 1.62/0.58  fof(f114,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(X1,sK2) | ~m1_subset_1(k1_mcart_1(X0),sK0) | k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.62/0.58    inference(superposition,[],[f78,f47])).
% 1.62/0.58  fof(f78,plain,(
% 1.62/0.58    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X5) )),
% 1.62/0.58    inference(definition_unfolding,[],[f32,f52])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X5) )),
% 1.62/0.58    inference(cnf_transformation,[],[f22])).
% 1.62/0.58  fof(f104,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f92])).
% 1.62/0.58  fof(f92,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X3) )),
% 1.62/0.58    inference(definition_unfolding,[],[f73,f76])).
% 1.62/0.58  fof(f76,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f60,f54])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.62/0.58  fof(f73,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X3) )),
% 1.62/0.58    inference(cnf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.62/0.58  fof(f213,plain,(
% 1.62/0.58    ( ! [X6] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X6)) )),
% 1.62/0.58    inference(superposition,[],[f105,f192])).
% 1.62/0.58  fof(f105,plain,(
% 1.62/0.58    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 1.62/0.58    inference(equality_resolution,[],[f93])).
% 1.62/0.58  fof(f93,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X2) )),
% 1.62/0.58    inference(definition_unfolding,[],[f72,f76])).
% 1.62/0.58  fof(f72,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f18])).
% 1.62/0.58  fof(f201,plain,(
% 1.62/0.58    ( ! [X2] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2) | k1_xboole_0 = X2) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f200,f36])).
% 1.62/0.58  fof(f200,plain,(
% 1.62/0.58    ( ! [X2] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2) | k1_xboole_0 = sK2 | k1_xboole_0 = X2) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f199,f35])).
% 1.62/0.58  fof(f199,plain,(
% 1.62/0.58    ( ! [X2] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X2) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f191,f34])).
% 1.62/0.58  fof(f191,plain,(
% 1.62/0.58    ( ! [X2] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X2) )),
% 1.62/0.58    inference(superposition,[],[f96,f178])).
% 1.62/0.58  fof(f96,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.62/0.58    inference(definition_unfolding,[],[f69,f76])).
% 1.62/0.58  fof(f69,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.62/0.58    inference(cnf_transformation,[],[f18])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    k1_xboole_0 != sK2),
% 1.62/0.58    inference(cnf_transformation,[],[f22])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (12095)------------------------------
% 1.62/0.58  % (12095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (12095)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (12095)Memory used [KB]: 1918
% 1.62/0.58  % (12095)Time elapsed: 0.169 s
% 1.62/0.58  % (12095)------------------------------
% 1.62/0.58  % (12095)------------------------------
% 1.62/0.58  % (12074)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (12074)Memory used [KB]: 1791
% 1.62/0.58  % (12074)Time elapsed: 0.145 s
% 1.62/0.58  % (12074)------------------------------
% 1.62/0.58  % (12074)------------------------------
% 1.62/0.58  % (12073)Success in time 0.21 s
%------------------------------------------------------------------------------
