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
% DateTime   : Thu Dec  3 12:59:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 573 expanded)
%              Number of leaves         :   15 ( 128 expanded)
%              Depth                    :   24
%              Number of atoms          :  334 (2775 expanded)
%              Number of equality atoms :  200 (1669 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f291,plain,(
    $false ),
    inference(subsumption_resolution,[],[f290,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f290,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f289,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f289,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f288,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f288,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(condensation,[],[f287])).

fof(f287,plain,(
    ! [X6] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X6 ) ),
    inference(subsumption_resolution,[],[f250,f189])).

fof(f189,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f188,f149])).

fof(f149,plain,(
    ! [X2] :
      ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f146,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f146,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
      | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ) ),
    inference(resolution,[],[f145,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f145,plain,
    ( v1_xboole_0(k1_xboole_0)
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(superposition,[],[f135,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f55,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f135,plain,(
    ! [X2] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2))
      | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f134,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f134,plain,(
    ! [X2] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2))
      | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ) ),
    inference(resolution,[],[f116,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X0)) ) ),
    inference(resolution,[],[f90,f46])).

fof(f90,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f65,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f65,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f188,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f187,f104])).

fof(f104,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f38,f99])).

fof(f99,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f98,f35])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f89,f36])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(resolution,[],[f65,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    inference(cnf_transformation,[],[f20])).

fof(f187,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
      | sK3 = k2_mcart_1(sK4)
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f183,f103])).

fof(f103,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f84,f99])).

fof(f84,plain,(
    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) ),
    inference(resolution,[],[f65,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(definition_unfolding,[],[f58,f49])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | sK3 = X0
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ) ),
    inference(subsumption_resolution,[],[f182,f107])).

fof(f107,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(backward_demodulation,[],[f86,f93])).

fof(f93,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f87,f36])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f65,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f52,f49])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(definition_unfolding,[],[f56,f49])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f182,plain,(
    ! [X0,X1] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ) ),
    inference(subsumption_resolution,[],[f179,f110])).

fof(f110,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(backward_demodulation,[],[f85,f96])).

fof(f96,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f94,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f88,f36])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f65,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) ),
    inference(resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(definition_unfolding,[],[f57,f49])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f179,plain,(
    ! [X0,X1] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f66,f178])).

fof(f178,plain,(
    ! [X2] :
      ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f175,f39])).

fof(f175,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
      | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ) ),
    inference(resolution,[],[f174,f46])).

fof(f174,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f140,f80])).

fof(f140,plain,(
    ! [X2] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2))
      | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ) ),
    inference(subsumption_resolution,[],[f139,f42])).

fof(f139,plain,(
    ! [X2] :
      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2))
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
      | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ) ),
    inference(resolution,[],[f132,f45])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X0)) ) ),
    inference(resolution,[],[f116,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f66,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f33,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f250,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X6 ) ),
    inference(superposition,[],[f77,f226])).

fof(f226,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f225,f121])).

fof(f121,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(resolution,[],[f117,f45])).

fof(f117,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f90,f39])).

fof(f225,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f224,f104])).

fof(f224,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | sK3 = k2_mcart_1(sK4)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f166,f103])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | sK3 = X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f165,f107])).

fof(f165,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f162,f110])).

fof(f162,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ) ),
    inference(superposition,[],[f66,f126])).

fof(f126,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(resolution,[],[f118,f45])).

fof(f118,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f117,f50])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (15510)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (15526)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (15535)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (15532)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (15516)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (15519)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (15508)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15512)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (15524)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (15509)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (15516)Refutation not found, incomplete strategy% (15516)------------------------------
% 0.21/0.53  % (15516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15530)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (15516)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15516)Memory used [KB]: 10618
% 0.21/0.53  % (15516)Time elapsed: 0.121 s
% 0.21/0.53  % (15516)------------------------------
% 0.21/0.53  % (15516)------------------------------
% 0.21/0.53  % (15506)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (15506)Refutation not found, incomplete strategy% (15506)------------------------------
% 0.21/0.53  % (15506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15506)Memory used [KB]: 1663
% 0.21/0.53  % (15506)Time elapsed: 0.115 s
% 0.21/0.53  % (15506)------------------------------
% 0.21/0.53  % (15506)------------------------------
% 0.21/0.53  % (15515)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (15527)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (15513)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (15507)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (15511)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (15531)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15514)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (15522)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (15520)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (15529)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (15533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15508)Refutation not found, incomplete strategy% (15508)------------------------------
% 0.21/0.54  % (15508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15508)Memory used [KB]: 10746
% 0.21/0.54  % (15508)Time elapsed: 0.122 s
% 0.21/0.54  % (15508)------------------------------
% 0.21/0.54  % (15508)------------------------------
% 0.21/0.54  % (15529)Refutation not found, incomplete strategy% (15529)------------------------------
% 0.21/0.54  % (15529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15529)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15529)Memory used [KB]: 1791
% 0.21/0.54  % (15529)Time elapsed: 0.089 s
% 0.21/0.54  % (15529)------------------------------
% 0.21/0.54  % (15529)------------------------------
% 0.21/0.54  % (15521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (15523)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (15515)Refutation not found, incomplete strategy% (15515)------------------------------
% 0.21/0.54  % (15515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15523)Refutation not found, incomplete strategy% (15523)------------------------------
% 0.21/0.54  % (15523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15515)Memory used [KB]: 10618
% 0.21/0.54  % (15515)Time elapsed: 0.139 s
% 0.21/0.54  % (15515)------------------------------
% 0.21/0.54  % (15515)------------------------------
% 0.21/0.55  % (15525)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (15523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15523)Memory used [KB]: 10618
% 0.21/0.55  % (15523)Time elapsed: 0.136 s
% 0.21/0.55  % (15523)------------------------------
% 0.21/0.55  % (15523)------------------------------
% 0.21/0.55  % (15528)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (15536)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (15528)Refutation not found, incomplete strategy% (15528)------------------------------
% 0.21/0.55  % (15528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15518)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (15527)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (15517)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (15528)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15528)Memory used [KB]: 10746
% 0.21/0.56  % (15528)Time elapsed: 0.141 s
% 0.21/0.56  % (15528)------------------------------
% 0.21/0.56  % (15528)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f290,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    k1_xboole_0 != sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.57    inference(negated_conjecture,[],[f17])).
% 0.21/0.57  fof(f17,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    k1_xboole_0 = sK2),
% 0.21/0.57    inference(subsumption_resolution,[],[f289,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f289,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.57    inference(subsumption_resolution,[],[f288,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f288,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.57    inference(condensation,[],[f287])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    ( ! [X6] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X6) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f250,f189])).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f188,f149])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    ( ! [X2] : (sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 0.21/0.57    inference(resolution,[],[f146,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))) )),
% 0.21/0.57    inference(resolution,[],[f145,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.21/0.57    inference(superposition,[],[f135,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X3) )),
% 0.21/0.57    inference(definition_unfolding,[],[f63,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f55,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X3) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    ( ! [X2] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f134,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X2] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))) )),
% 0.21/0.57    inference(resolution,[],[f116,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X0))) )),
% 0.21/0.57    inference(resolution,[],[f90,f46])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.57    inference(resolution,[],[f65,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.57    inference(definition_unfolding,[],[f34,f49])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f187,f104])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    sK3 != k2_mcart_1(sK4)),
% 0.21/0.57    inference(superposition,[],[f38,f99])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f98,f35])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f97,f37])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f89,f36])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.57    inference(resolution,[],[f65,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f49])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(resolution,[],[f183,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.21/0.57    inference(backward_demodulation,[],[f84,f99])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)),
% 0.21/0.57    inference(resolution,[],[f65,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f58,f49])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f182,f107])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f86,f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f92,f35])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f91,f37])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f87,f36])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(resolution,[],[f65,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f52,f49])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.57    inference(resolution,[],[f65,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f56,f49])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f179,f110])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f85,f96])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f95,f35])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f94,f37])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(subsumption_resolution,[],[f88,f36])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.57    inference(resolution,[],[f65,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f53,f49])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)),
% 0.21/0.57    inference(resolution,[],[f65,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f57,f49])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 0.21/0.57  fof(f179,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(superposition,[],[f66,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    ( ! [X2] : (k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 0.21/0.57    inference(resolution,[],[f175,f39])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))) )),
% 0.21/0.57    inference(resolution,[],[f174,f46])).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(superposition,[],[f140,f80])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ( ! [X2] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f139,f42])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X2] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))) )),
% 0.21/0.57    inference(resolution,[],[f132,f45])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X0))) )),
% 0.21/0.57    inference(resolution,[],[f116,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.21/0.57    inference(definition_unfolding,[],[f33,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f250,plain,(
% 0.21/0.57    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = X6) )),
% 0.21/0.57    inference(superposition,[],[f77,f226])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f225,f121])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f120,f42])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.21/0.57    inference(resolution,[],[f117,f45])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(resolution,[],[f90,f39])).
% 0.21/0.57  fof(f225,plain,(
% 0.21/0.57    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f224,f104])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(resolution,[],[f166,f103])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f165,f107])).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f162,f110])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )),
% 0.21/0.57    inference(superposition,[],[f66,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f125,f42])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.57    inference(resolution,[],[f118,f45])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.57    inference(resolution,[],[f117,f50])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.57    inference(definition_unfolding,[],[f59,f64])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (15527)------------------------------
% 0.21/0.57  % (15527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15527)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (15527)Memory used [KB]: 1918
% 0.21/0.57  % (15527)Time elapsed: 0.161 s
% 0.21/0.57  % (15527)------------------------------
% 0.21/0.57  % (15527)------------------------------
% 0.21/0.57  % (15502)Success in time 0.212 s
%------------------------------------------------------------------------------
