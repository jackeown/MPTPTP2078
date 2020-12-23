%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0903+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 496 expanded)
%              Number of leaves         :   31 ( 178 expanded)
%              Depth                    :   10
%              Number of atoms          :  486 (1349 expanded)
%              Number of equality atoms :  161 ( 601 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f544,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f118,f154,f165,f173,f218,f235,f273,f287,f294,f425,f469,f483,f491,f494,f538])).

fof(f538,plain,
    ( ~ spl6_16
    | spl6_9
    | spl6_7
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f536,f300,f134,f141,f200])).

fof(f200,plain,
    ( spl6_16
  <=> m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f141,plain,
    ( spl6_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f134,plain,
    ( spl6_7
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f300,plain,
    ( spl6_19
  <=> sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f536,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_19 ),
    inference(trivial_inequality_removal,[],[f533])).

fof(f533,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | sK4(sK0) != sK4(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_19 ),
    inference(resolution,[],[f333,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) ) ),
    inference(definition_unfolding,[],[f71,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),X0)
        | o_0_0_xboole_0 = X0
        | v1_xboole_0(X0)
        | sK4(X0) != sK4(sK0) )
    | ~ spl6_19 ),
    inference(resolution,[],[f327,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f327,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),X4)
        | sK4(sK0) != sK4(X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl6_19 ),
    inference(superposition,[],[f78,f301])).

fof(f301,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f300])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5)
      | ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f72,f46])).

fof(f46,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f62,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f494,plain,
    ( spl6_7
    | spl6_12
    | spl6_13
    | spl6_11
    | spl6_19
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f493,f200,f300,f177,f183,f180,f134])).

fof(f180,plain,
    ( spl6_12
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f183,plain,
    ( spl6_13
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f177,plain,
    ( spl6_11
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f493,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)),k9_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k10_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0))),k11_mcart_1(sK0,sK1,sK2,sK3,sK4(sK0)))
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | ~ spl6_16 ),
    inference(resolution,[],[f201,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f69,f72,f63,f46,f46,f46,f46])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f201,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f200])).

fof(f491,plain,
    ( spl6_7
    | spl6_16
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f489,f96,f200,f134])).

fof(f96,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f489,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | o_0_0_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(resolution,[],[f472,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f472,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f431,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f431,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)))
    | ~ spl6_1 ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f483,plain,
    ( ~ spl6_1
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f73,f479])).

fof(f479,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(resolution,[],[f478,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,o_0_0_xboole_0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f46,f46])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f478,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f476,f93])).

fof(f93,plain,(
    ! [X2,X0,X3] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,o_0_0_xboole_0),X2,X3) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f66,f46,f46,f63])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f476,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK2,sK3))
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f97,f181])).

fof(f181,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f73,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    & ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
      | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
      | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
      | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
          | r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
          | r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
          | r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) ) )
   => ( k1_xboole_0 != sK0
      & ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
        | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
        | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
        | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
        | r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
        | r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
        | r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ ( ~ r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
            & ~ r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
            & ~ r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
            & ~ r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X0,k4_zfmisc_1(X3,X0,X1,X2))
          & ~ r1_tarski(X0,k4_zfmisc_1(X2,X3,X0,X1))
          & ~ r1_tarski(X0,k4_zfmisc_1(X1,X2,X3,X0))
          & ~ r1_tarski(X0,k4_zfmisc_1(X0,X1,X2,X3)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_mcart_1)).

fof(f469,plain,
    ( ~ spl6_1
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f73,f464])).

fof(f464,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(resolution,[],[f458,f76])).

fof(f458,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f432,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),o_0_0_xboole_0,X3) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f67,f46,f46,f63])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f432,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0,sK3))
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f97,f184])).

fof(f184,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f425,plain,
    ( ~ spl6_8
    | spl6_9
    | spl6_7
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f424,f186,f134,f141,f137])).

fof(f137,plain,
    ( spl6_8
  <=> m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f186,plain,
    ( spl6_14
  <=> sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f424,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_14 ),
    inference(trivial_inequality_removal,[],[f421])).

fof(f421,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0)
    | sK4(sK0) != sK4(sK0)
    | ~ m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_14 ),
    inference(resolution,[],[f332,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) ) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),X0)
        | o_0_0_xboole_0 = X0
        | v1_xboole_0(X0)
        | sK4(X0) != sK4(sK0) )
    | ~ spl6_14 ),
    inference(resolution,[],[f322,f53])).

fof(f322,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),X5)
        | sK4(sK0) != sK4(X5)
        | o_0_0_xboole_0 = X5 )
    | ~ spl6_14 ),
    inference(superposition,[],[f77,f187])).

fof(f187,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5)
      | ~ r2_hidden(X3,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f72,f46])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f294,plain,
    ( spl6_11
    | spl6_7
    | spl6_12
    | spl6_13
    | spl6_14
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f293,f137,f186,f183,f180,f134,f177])).

fof(f293,plain,
    ( sK4(sK0) = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)),k9_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k10_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0))),k11_mcart_1(sK3,sK0,sK1,sK2,sK4(sK0)))
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK3
    | ~ spl6_8 ),
    inference(resolution,[],[f138,f88])).

fof(f138,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f287,plain,
    ( ~ spl6_4
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f73,f283])).

fof(f283,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(resolution,[],[f282,f76])).

fof(f282,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f280,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X3
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f68,f46,f46,f63])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f280,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f106,f184])).

fof(f106,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_4
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f273,plain,
    ( ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f73,f269])).

fof(f269,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(resolution,[],[f268,f76])).

fof(f268,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f265,f92])).

fof(f265,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),o_0_0_xboole_0,sK2))
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f106,f181])).

fof(f235,plain,
    ( ~ spl6_1
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f73,f231])).

fof(f231,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(resolution,[],[f224,f76])).

fof(f224,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f223,f91])).

fof(f223,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,o_0_0_xboole_0))
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f97,f178])).

fof(f178,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f218,plain,
    ( ~ spl6_4
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f73,f214])).

fof(f214,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(resolution,[],[f211,f76])).

fof(f211,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f208,f94])).

fof(f94,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1),X2,X3) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ) ),
    inference(definition_unfolding,[],[f65,f46,f46,f63])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f208,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK0),sK1,sK2))
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f106,f178])).

fof(f173,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f171,f105,f137,f134])).

fof(f171,plain,
    ( m1_subset_1(sK4(sK0),k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | o_0_0_xboole_0 = sK0
    | ~ spl6_4 ),
    inference(resolution,[],[f122,f79])).

fof(f122,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | m1_subset_1(X1,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f120,f57])).

fof(f120,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2)))
    | ~ spl6_4 ),
    inference(resolution,[],[f106,f55])).

fof(f165,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f73,f147])).

fof(f147,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(resolution,[],[f142,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f142,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f154,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f73,f135])).

fof(f135,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f118,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f73,f114])).

fof(f114,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(resolution,[],[f103,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f103,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_3
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f112,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f73,f108])).

fof(f108,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(resolution,[],[f100,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_2
  <=> r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

% (3439)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f107,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f74,f105,f102,f99,f96])).

fof(f74,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK3,sK0),sK1,sK2))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK0,sK1))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3,sK0))
    | r1_tarski(sK0,k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)) ),
    inference(definition_unfolding,[],[f43,f63,f63,f63,f63])).

fof(f43,plain,
    ( r1_tarski(sK0,k4_zfmisc_1(sK3,sK0,sK1,sK2))
    | r1_tarski(sK0,k4_zfmisc_1(sK2,sK3,sK0,sK1))
    | r1_tarski(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK0))
    | r1_tarski(sK0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
