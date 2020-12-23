%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 216 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   37
%              Number of atoms          :  343 (1046 expanded)
%              Number of equality atoms :  154 ( 490 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f196,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f196,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f195,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f195,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f194,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f194,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(condensation,[],[f193])).

fof(f193,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f183,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f183,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f86,f175])).

fof(f175,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f166,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f166,plain,(
    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f163,f97])).

fof(f97,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f77,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f163,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f158,f43])).

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

fof(f158,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f156,f97])).

fof(f156,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(X6,sK2))
      | ~ r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f151,f43])).

fof(f151,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2)) ) ),
    inference(resolution,[],[f150,f97])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f149,f98])).

fof(f98,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f96,f77])).

fof(f96,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f93,f37])).

fof(f93,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f39,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f39,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,k2_zfmisc_1(X0,sK2))
      | sK3 = k2_mcart_1(sK4)
      | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1)) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK2))
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2)) ) ),
    inference(condensation,[],[f147])).

fof(f147,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK4 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X4)) ) ),
    inference(resolution,[],[f146,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | sK4 != X0
      | ~ r2_hidden(X0,X1)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)) ) ),
    inference(resolution,[],[f145,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,sK1))
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2)) ) ),
    inference(resolution,[],[f143,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,sK1))
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f140,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f140,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | sK3 = X1
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f139,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | sK3 = X1 ) ),
    inference(subsumption_resolution,[],[f138,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(sK0,sK1))
      | sK3 = X2
      | ~ r2_hidden(X0,X1)
      | sK4 != k4_tarski(X0,X2)
      | ~ m1_subset_1(X2,sK2) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK3 = X2
      | ~ r1_tarski(X1,k2_zfmisc_1(sK0,sK1))
      | sK4 != k4_tarski(X0,X2)
      | ~ m1_subset_1(X2,sK2)
      | ~ r1_tarski(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(condensation,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK3 = X2
      | ~ r1_tarski(X1,k2_zfmisc_1(sK0,sK1))
      | sK4 != k4_tarski(X0,X2)
      | ~ m1_subset_1(X2,sK2)
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f131,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(X3,sK1,X1),sK0)
      | ~ r2_hidden(X1,X2)
      | sK3 = X0
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK1))
      | sK4 != k4_tarski(X1,X0)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f126,f51])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X3,sK1,X0),sK0)
      | ~ m1_subset_1(X2,sK2)
      | ~ r2_hidden(X0,X1)
      | sK3 = X2
      | ~ r1_tarski(X1,k2_zfmisc_1(X3,sK1))
      | sK4 != k4_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(sK7(X3,sK1,X0),sK0)
      | sK3 = X2
      | ~ r1_tarski(X1,k2_zfmisc_1(X3,sK1))
      | sK4 != k4_tarski(X0,X2)
      | ~ r1_tarski(X1,k2_zfmisc_1(X3,sK1)) ) ),
    inference(condensation,[],[f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(sK7(X1,sK1,X2),sK0)
      | sK3 = X0
      | ~ r2_hidden(X2,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(X1,sK1))
      | sK4 != k4_tarski(X2,X0)
      | ~ r2_hidden(X2,X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X1,sK1)) ) ),
    inference(resolution,[],[f107,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK8(X2,X3,X0),sK1)
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(sK7(X2,X3,X0),sK0)
      | sK3 = X1
      | ~ r2_hidden(X0,X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | k4_tarski(X0,X1) != sK4 ) ),
    inference(resolution,[],[f100,f51])).

fof(f100,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ m1_subset_1(sK8(X3,X4,X5),sK1)
      | sK4 != k4_tarski(X5,X6)
      | ~ m1_subset_1(X6,sK2)
      | ~ m1_subset_1(sK7(X3,X4,X5),sK0)
      | sK3 = X6
      | ~ r2_hidden(X5,X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f78,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f34,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(X1,sK2)
      | sK3 = X1
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f137,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X2,k2_zfmisc_1(sK0,sK1)),X2)
      | ~ r2_hidden(X1,X2)
      | sK4 != k4_tarski(X1,X0)
      | ~ m1_subset_1(X0,sK2)
      | sK3 = X0 ) ),
    inference(resolution,[],[f136,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (17901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (17913)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (17917)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (17906)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (17923)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (17908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (17915)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (17916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (17902)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (17925)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (17912)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (17907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (17928)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (17924)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (17904)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (17903)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (17926)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (17930)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (17927)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (17929)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (17919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (17920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (17923)Refutation not found, incomplete strategy% (17923)------------------------------
% 0.21/0.54  % (17923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17923)Memory used [KB]: 10874
% 0.21/0.54  % (17923)Time elapsed: 0.087 s
% 0.21/0.54  % (17923)------------------------------
% 0.21/0.54  % (17923)------------------------------
% 0.21/0.54  % (17922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (17909)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (17918)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (17921)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (17910)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (17918)Refutation not found, incomplete strategy% (17918)------------------------------
% 0.21/0.55  % (17918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17918)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17918)Memory used [KB]: 10618
% 0.21/0.55  % (17918)Time elapsed: 0.140 s
% 0.21/0.55  % (17918)------------------------------
% 0.21/0.55  % (17918)------------------------------
% 0.21/0.55  % (17922)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f196,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f20])).
% 0.21/0.55  fof(f20,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    k1_xboole_0 = sK2),
% 0.21/0.55    inference(subsumption_resolution,[],[f195,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.55    inference(subsumption_resolution,[],[f194,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.55    inference(condensation,[],[f193])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f183,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(superposition,[],[f86,f175])).
% 0.21/0.55  fof(f175,plain,(
% 0.21/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.55    inference(resolution,[],[f166,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(resolution,[],[f163,f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(resolution,[],[f77,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(definition_unfolding,[],[f35,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f158,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 0.21/0.55    inference(resolution,[],[f156,f97])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    ( ! [X6,X7] : (~r2_hidden(sK4,k2_zfmisc_1(X6,sK2)) | ~r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) )),
% 0.21/0.55    inference(resolution,[],[f151,f43])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~r2_hidden(sK4,k2_zfmisc_1(X0,sK2))) )),
% 0.21/0.55    inference(resolution,[],[f150,f97])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1)) | ~r2_hidden(sK4,k2_zfmisc_1(X0,sK2))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f149,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f96,f77])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(subsumption_resolution,[],[f95,f36])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f94,f38])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f93,f37])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(superposition,[],[f39,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f65,f60])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(X0,sK2)) | sK3 = k2_mcart_1(sK4) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f148])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,sK2)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2))) )),
% 0.21/0.55    inference(condensation,[],[f147])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (sK4 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X3,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X4))) )),
% 0.21/0.55    inference(resolution,[],[f146,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | sK4 != X0 | ~r2_hidden(X0,X1) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,k2_zfmisc_1(X2,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3))) )),
% 0.21/0.55    inference(resolution,[],[f145,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,sK1)) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK2))) )),
% 0.21/0.55    inference(resolution,[],[f143,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,sK1)) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(superposition,[],[f140,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK4 | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | sK3 = X1 | ~r2_hidden(X1,sK2)) )),
% 0.21/0.55    inference(resolution,[],[f139,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | sK3 = X1) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f138,f136])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(sK0,sK1)) | sK3 = X2 | ~r2_hidden(X0,X1) | sK4 != k4_tarski(X0,X2) | ~m1_subset_1(X2,sK2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | sK3 = X2 | ~r1_tarski(X1,k2_zfmisc_1(sK0,sK1)) | sK4 != k4_tarski(X0,X2) | ~m1_subset_1(X2,sK2) | ~r1_tarski(X1,k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.55    inference(condensation,[],[f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | sK3 = X2 | ~r1_tarski(X1,k2_zfmisc_1(sK0,sK1)) | sK4 != k4_tarski(X0,X2) | ~m1_subset_1(X2,sK2) | ~r2_hidden(X0,X3) | ~r1_tarski(X3,k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f131,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK7(X3,sK1,X1),sK0) | ~r2_hidden(X1,X2) | sK3 = X0 | ~r1_tarski(X2,k2_zfmisc_1(X3,sK1)) | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2)) )),
% 0.21/0.55    inference(resolution,[],[f126,f51])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X3,sK1,X0),sK0) | ~m1_subset_1(X2,sK2) | ~r2_hidden(X0,X1) | sK3 = X2 | ~r1_tarski(X1,k2_zfmisc_1(X3,sK1)) | sK4 != k4_tarski(X0,X2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X2,sK2) | ~m1_subset_1(sK7(X3,sK1,X0),sK0) | sK3 = X2 | ~r1_tarski(X1,k2_zfmisc_1(X3,sK1)) | sK4 != k4_tarski(X0,X2) | ~r1_tarski(X1,k2_zfmisc_1(X3,sK1))) )),
% 0.21/0.55    inference(condensation,[],[f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(sK7(X1,sK1,X2),sK0) | sK3 = X0 | ~r2_hidden(X2,X3) | ~r1_tarski(X3,k2_zfmisc_1(X1,sK1)) | sK4 != k4_tarski(X2,X0) | ~r2_hidden(X2,X4) | ~r1_tarski(X4,k2_zfmisc_1(X1,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f107,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK8(X2,X3,X0),sK1) | ~m1_subset_1(X1,sK2) | ~m1_subset_1(sK7(X2,X3,X0),sK0) | sK3 = X1 | ~r2_hidden(X0,X4) | ~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k4_tarski(X0,X1) != sK4) )),
% 0.21/0.55    inference(resolution,[],[f100,f51])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X6,X4,X7,X5,X3] : (~m1_subset_1(sK8(X3,X4,X5),sK1) | sK4 != k4_tarski(X5,X6) | ~m1_subset_1(X6,sK2) | ~m1_subset_1(sK7(X3,X4,X5),sK0) | sK3 = X6 | ~r2_hidden(X5,X7) | ~r1_tarski(X7,k2_zfmisc_1(X3,X4))) )),
% 0.21/0.55    inference(superposition,[],[f78,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3 | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.21/0.55    inference(definition_unfolding,[],[f34,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(X1,sK2) | sK3 = X1 | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f137,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK6(X2,k2_zfmisc_1(sK0,sK1)),X2) | ~r2_hidden(X1,X2) | sK4 != k4_tarski(X1,X0) | ~m1_subset_1(X0,sK2) | sK3 = X0) )),
% 0.21/0.55    inference(resolution,[],[f136,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f67,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f66,f60])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (17922)------------------------------
% 0.21/0.55  % (17922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17922)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (17922)Memory used [KB]: 1791
% 0.21/0.55  % (17922)Time elapsed: 0.145 s
% 0.21/0.55  % (17922)------------------------------
% 0.21/0.55  % (17922)------------------------------
% 0.21/0.55  % (17921)Refutation not found, incomplete strategy% (17921)------------------------------
% 0.21/0.55  % (17921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17921)Memory used [KB]: 10746
% 0.21/0.55  % (17921)Time elapsed: 0.139 s
% 0.21/0.55  % (17921)------------------------------
% 0.21/0.55  % (17921)------------------------------
% 0.21/0.55  % (17914)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (17900)Success in time 0.193 s
%------------------------------------------------------------------------------
