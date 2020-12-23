%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 (1730 expanded)
%              Number of leaves         :   15 ( 441 expanded)
%              Depth                    :   26
%              Number of atoms          :  290 (7237 expanded)
%              Number of equality atoms :  157 (4405 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f205,f56])).

fof(f56,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f205,plain,(
    o_0_0_xboole_0 = sK1 ),
    inference(resolution,[],[f200,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f200,plain,(
    v1_xboole_0(sK1) ),
    inference(forward_demodulation,[],[f196,f180])).

fof(f180,plain,(
    sK1 = k2_relat_1(o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f179,f57])).

fof(f57,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f179,plain,
    ( sK1 = k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f166,f56])).

fof(f166,plain,
    ( sK1 = k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(superposition,[],[f61,f142])).

fof(f142,plain,(
    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f55,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | o_0_0_xboole_0 = sK2 ),
    inference(resolution,[],[f139,f60])).

fof(f139,plain,
    ( v1_xboole_0(sK2)
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f138,f55])).

fof(f138,plain,
    ( v1_xboole_0(sK2)
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f135,f61])).

fof(f135,plain,(
    v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(subsumption_resolution,[],[f134,f106])).

fof(f106,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(subsumption_resolution,[],[f105,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f105,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) ),
    inference(resolution,[],[f101,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f101,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f75,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f58,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f32,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f134,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(subsumption_resolution,[],[f133,f89])).

fof(f89,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f36,f84])).

fof(f84,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f83,f57])).

fof(f83,plain,
    ( o_0_0_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f82,f55])).

fof(f82,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f74,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(resolution,[],[f58,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f51,f37,f37,f37,f46])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f36,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,
    ( sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | sK3 = k2_mcart_1(sK4)
    | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(resolution,[],[f129,f88])).

fof(f88,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(backward_demodulation,[],[f69,f84])).

fof(f69,plain,(
    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) ),
    inference(resolution,[],[f58,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(definition_unfolding,[],[f54,f46])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | sK3 = X0
      | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ) ),
    inference(subsumption_resolution,[],[f128,f92])).

fof(f92,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(backward_demodulation,[],[f71,f78])).

fof(f78,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f77,f57])).

fof(f77,plain,
    ( o_0_0_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f76,f55])).

fof(f76,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f72,f56])).

fof(f72,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f49,f37,f37,f37,f46])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f128,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ) ),
    inference(subsumption_resolution,[],[f127,f95])).

fof(f95,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(backward_demodulation,[],[f70,f81])).

fof(f81,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f80,f57])).

fof(f80,plain,
    ( o_0_0_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f79,f55])).

fof(f79,plain,
    ( o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f73,f56])).

fof(f73,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f58,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f50,f37,f37,f37,f46])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f127,plain,(
    ! [X0] :
      ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
      | sK3 = X0
      | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ) ),
    inference(superposition,[],[f59,f111])).

fof(f111,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(subsumption_resolution,[],[f110,f40])).

fof(f110,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(resolution,[],[f103,f41])).

fof(f103,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f59,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f31,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f37,f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f196,plain,(
    v1_xboole_0(k2_relat_1(o_0_0_xboole_0)) ),
    inference(backward_demodulation,[],[f190,f191])).

fof(f191,plain,(
    o_0_0_xboole_0 = k2_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)) ),
    inference(resolution,[],[f162,f60])).

fof(f162,plain,(
    v1_xboole_0(k2_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2))) ),
    inference(backward_demodulation,[],[f135,f142])).

fof(f190,plain,(
    v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))) ),
    inference(resolution,[],[f162,f39])).

% (24483)Refutation not found, incomplete strategy% (24483)------------------------------
% (24483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24497)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (24489)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (24497)Refutation not found, incomplete strategy% (24497)------------------------------
% 0.21/0.50  % (24497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24481)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (24489)Refutation not found, incomplete strategy% (24489)------------------------------
% 0.21/0.50  % (24489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24489)Memory used [KB]: 6268
% 0.21/0.50  % (24489)Time elapsed: 0.054 s
% 0.21/0.50  % (24489)------------------------------
% 0.21/0.50  % (24489)------------------------------
% 0.21/0.50  % (24497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24497)Memory used [KB]: 1791
% 0.21/0.50  % (24497)Time elapsed: 0.044 s
% 0.21/0.50  % (24497)------------------------------
% 0.21/0.50  % (24497)------------------------------
% 0.21/0.51  % (24478)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24478)Refutation not found, incomplete strategy% (24478)------------------------------
% 0.21/0.52  % (24478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24478)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24478)Memory used [KB]: 6268
% 0.21/0.52  % (24478)Time elapsed: 0.099 s
% 0.21/0.52  % (24478)------------------------------
% 0.21/0.52  % (24478)------------------------------
% 0.21/0.52  % (24474)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (24474)Refutation not found, incomplete strategy% (24474)------------------------------
% 0.21/0.52  % (24474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24474)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24474)Memory used [KB]: 1663
% 0.21/0.52  % (24474)Time elapsed: 0.098 s
% 0.21/0.52  % (24474)------------------------------
% 0.21/0.52  % (24474)------------------------------
% 0.21/0.52  % (24479)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (24480)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (24475)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (24485)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (24502)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (24487)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (24492)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (24488)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (24496)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (24486)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24498)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24500)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (24476)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (24490)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (24499)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (24503)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (24493)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (24495)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (24477)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (24491)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (24483)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (24495)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f205,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    o_0_0_xboole_0 != sK1),
% 0.21/0.55    inference(definition_unfolding,[],[f34,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f15])).
% 0.21/0.55  fof(f15,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK1),
% 0.21/0.55    inference(resolution,[],[f200,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f38,f37])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    v1_xboole_0(sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f196,f180])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    sK1 = k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f179,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    o_0_0_xboole_0 != sK0),
% 0.21/0.55    inference(definition_unfolding,[],[f33,f37])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    sK1 = k2_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f166,f56])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    sK1 = k2_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK0),
% 0.21/0.55    inference(superposition,[],[f61,f142])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f141,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    o_0_0_xboole_0 != sK2),
% 0.21/0.55    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) | o_0_0_xboole_0 = sK2),
% 0.21/0.55    inference(resolution,[],[f139,f60])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    v1_xboole_0(sK2) | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f138,f55])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    v1_xboole_0(sK2) | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.55    inference(superposition,[],[f135,f61])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f134,f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f105,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))),
% 0.21/0.55    inference(resolution,[],[f101,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(resolution,[],[f75,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(resolution,[],[f58,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.55    inference(definition_unfolding,[],[f32,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK4)),
% 0.21/0.55    inference(superposition,[],[f36,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f83,f57])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f82,f55])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f74,f56])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 0.21/0.55    inference(resolution,[],[f58,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f51,f37,f37,f37,f46])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    sK4 != k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | sK3 = k2_mcart_1(sK4) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(resolution,[],[f129,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f69,f84])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2)),
% 0.21/0.55    inference(resolution,[],[f58,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f54,f46])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f128,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.21/0.55    inference(backward_demodulation,[],[f71,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f77,f57])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f76,f55])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f72,f56])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(resolution,[],[f58,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f49,f37,f37,f37,f46])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.55    inference(resolution,[],[f58,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f52,f46])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f127,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f70,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f80,f57])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f79,f55])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f73,f56])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    o_0_0_xboole_0 = sK1 | o_0_0_xboole_0 = sK2 | o_0_0_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.55    inference(resolution,[],[f58,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f50,f37,f37,f37,f46])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1)),
% 0.21/0.55    inference(resolution,[],[f58,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f46])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | sK3 = X0 | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) )),
% 0.21/0.55    inference(superposition,[],[f59,f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f110,f40])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.55    inference(resolution,[],[f103,f41])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))),
% 0.21/0.55    inference(resolution,[],[f101,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.21/0.55    inference(definition_unfolding,[],[f31,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f44,f37,f37])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(o_0_0_xboole_0))),
% 0.21/0.55    inference(backward_demodulation,[],[f190,f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    o_0_0_xboole_0 = k2_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2))),
% 0.21/0.55    inference(resolution,[],[f162,f60])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))),
% 0.21/0.55    inference(backward_demodulation,[],[f135,f142])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(o_0_0_xboole_0,sK2))))),
% 0.21/0.55    inference(resolution,[],[f162,f39])).
% 0.21/0.55  % (24483)Refutation not found, incomplete strategy% (24483)------------------------------
% 0.21/0.55  % (24483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (24483)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  % (24495)------------------------------
% 0.21/0.55  % (24495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  
% 0.21/0.55  % (24495)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (24483)Memory used [KB]: 10618
% 0.21/0.55  % (24483)Time elapsed: 0.130 s
% 0.21/0.55  % (24495)Memory used [KB]: 1791
% 0.21/0.55  % (24483)------------------------------
% 0.21/0.55  % (24483)------------------------------
% 0.21/0.55  % (24495)Time elapsed: 0.134 s
% 0.21/0.55  % (24495)------------------------------
% 0.21/0.55  % (24495)------------------------------
% 0.21/0.55  % (24473)Success in time 0.182 s
%------------------------------------------------------------------------------
