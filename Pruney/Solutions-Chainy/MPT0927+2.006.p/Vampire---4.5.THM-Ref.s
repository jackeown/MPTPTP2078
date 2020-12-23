%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:52 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 403 expanded)
%              Number of leaves         :   19 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  325 (1387 expanded)
%              Number of equality atoms :   89 ( 234 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f229,f240,f282,f320,f384,f450,f544,f579,f590,f601])).

fof(f601,plain,
    ( spl10_3
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | spl10_3
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f150,f591,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f591,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | spl10_3
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(forward_demodulation,[],[f117,f563])).

fof(f563,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f227,f215,f219,f223,f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f45,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f21,f43])).

fof(f21,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f223,plain,
    ( k1_xboole_0 != sK2
    | spl10_8 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl10_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f219,plain,
    ( k1_xboole_0 != sK3
    | spl10_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl10_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f215,plain,
    ( k1_xboole_0 != sK0
    | spl10_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl10_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f227,plain,
    ( k1_xboole_0 != sK1
    | spl10_9 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl10_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f117,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_3
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f150,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f74,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(unit_resulting_resolution,[],[f44,f40])).

fof(f44,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f22,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f590,plain,
    ( spl10_2
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl10_2
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f74,f581,f41])).

fof(f581,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | spl10_2
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f113,f281])).

fof(f281,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl10_10
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f113,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_2
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f579,plain,
    ( spl10_4
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | spl10_4
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f150,f570,f40])).

fof(f570,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | spl10_4
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(backward_demodulation,[],[f121,f562])).

fof(f562,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f227,f215,f219,f223,f45,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f27,f43])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f121,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_4
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f544,plain,(
    ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f39,f460,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f460,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))
    | ~ spl10_9 ),
    inference(backward_demodulation,[],[f242,f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f226])).

fof(f242,plain,(
    ~ r1_tarski(sK1,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) ),
    inference(unit_resulting_resolution,[],[f197,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f197,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK1) ),
    inference(unit_resulting_resolution,[],[f62,f183,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f183,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(unit_resulting_resolution,[],[f150,f41])).

fof(f62,plain,(
    r1_tarski(sK5,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f38])).

fof(f25,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f450,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f39,f393,f38])).

fof(f393,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f163,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f222])).

fof(f163,plain,(
    ~ r1_tarski(sK2,k2_mcart_1(k1_mcart_1(sK8))) ),
    inference(unit_resulting_resolution,[],[f158,f32])).

fof(f158,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2) ),
    inference(unit_resulting_resolution,[],[f53,f151,f33])).

fof(f151,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(unit_resulting_resolution,[],[f74,f41])).

fof(f53,plain,(
    r1_tarski(sK6,sK2) ),
    inference(unit_resulting_resolution,[],[f24,f38])).

fof(f24,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f384,plain,(
    ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f39,f328,f38])).

fof(f328,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(sK8))
    | ~ spl10_7 ),
    inference(backward_demodulation,[],[f87,f220])).

fof(f220,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f87,plain,(
    ~ r1_tarski(sK3,k2_mcart_1(sK8)) ),
    inference(unit_resulting_resolution,[],[f82,f32])).

fof(f82,plain,(
    r2_hidden(k2_mcart_1(sK8),sK3) ),
    inference(unit_resulting_resolution,[],[f50,f75,f33])).

fof(f75,plain,(
    r2_hidden(k2_mcart_1(sK8),sK7) ),
    inference(unit_resulting_resolution,[],[f44,f41])).

fof(f50,plain,(
    r1_tarski(sK7,sK3) ),
    inference(unit_resulting_resolution,[],[f23,f38])).

fof(f23,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f320,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f39,f291,f38])).

fof(f291,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f202,f216])).

fof(f216,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f202,plain,(
    ~ r1_tarski(sK0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) ),
    inference(unit_resulting_resolution,[],[f191,f32])).

fof(f191,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f182,f33])).

fof(f182,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    inference(unit_resulting_resolution,[],[f150,f40])).

fof(f65,plain,(
    r1_tarski(sK4,sK0) ),
    inference(unit_resulting_resolution,[],[f26,f38])).

fof(f26,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f282,plain,
    ( spl10_10
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f100,f226,f222,f218,f214,f279])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f240,plain,
    ( spl10_1
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl10_1
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f44,f230,f41])).

fof(f230,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | spl10_1
    | ~ spl10_5 ),
    inference(backward_demodulation,[],[f109,f212])).

fof(f212,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl10_5
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f109,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_1
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f229,plain,
    ( spl10_5
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f101,f226,f222,f218,f214,f210])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f20,f119,f115,f111,f107])).

fof(f20,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (28108)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.48  % (28100)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (28078)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28077)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (28079)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28106)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (28109)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28081)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28103)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28102)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (28101)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (28105)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28080)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (28082)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (28093)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (28104)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (28097)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (28097)Refutation not found, incomplete strategy% (28097)------------------------------
% 0.21/0.55  % (28097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28097)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28097)Memory used [KB]: 10618
% 0.21/0.55  % (28097)Time elapsed: 0.139 s
% 0.21/0.55  % (28097)------------------------------
% 0.21/0.55  % (28097)------------------------------
% 0.21/0.55  % (28098)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (28095)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.55  % (28096)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.55  % (28088)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  % (28085)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.55  % (28087)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.56  % (28090)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.56  % (28091)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.56  % (28094)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.56  % (28086)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.56  % (28090)Refutation not found, incomplete strategy% (28090)------------------------------
% 1.47/0.56  % (28090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28107)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.56  % (28090)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28090)Memory used [KB]: 10746
% 1.47/0.56  % (28090)Time elapsed: 0.151 s
% 1.47/0.56  % (28090)------------------------------
% 1.47/0.56  % (28090)------------------------------
% 1.62/0.57  % (28081)Refutation found. Thanks to Tanya!
% 1.62/0.57  % SZS status Theorem for theBenchmark
% 1.62/0.57  % (28092)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.57  % SZS output start Proof for theBenchmark
% 1.62/0.57  fof(f602,plain,(
% 1.62/0.57    $false),
% 1.62/0.57    inference(avatar_sat_refutation,[],[f122,f229,f240,f282,f320,f384,f450,f544,f579,f590,f601])).
% 1.62/0.57  fof(f601,plain,(
% 1.62/0.57    spl10_3 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f595])).
% 1.62/0.57  fof(f595,plain,(
% 1.62/0.57    $false | (spl10_3 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f150,f591,f41])).
% 1.62/0.57  fof(f41,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f19])).
% 1.62/0.57  fof(f19,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.62/0.57    inference(ennf_transformation,[],[f8])).
% 1.62/0.57  fof(f8,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.62/0.57  fof(f591,plain,(
% 1.62/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | (spl10_3 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 1.62/0.57    inference(forward_demodulation,[],[f117,f563])).
% 1.62/0.57  fof(f563,plain,(
% 1.62/0.57    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f227,f215,f219,f223,f45,f48])).
% 1.62/0.57  fof(f48,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f28,f43])).
% 1.62/0.57  fof(f43,plain,(
% 1.62/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f36,f42])).
% 1.62/0.57  fof(f42,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f6])).
% 1.62/0.57  fof(f6,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.62/0.57  fof(f36,plain,(
% 1.62/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f7])).
% 1.62/0.57  fof(f7,axiom,(
% 1.62/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.62/0.57  fof(f28,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f14])).
% 1.62/0.57  fof(f14,plain,(
% 1.62/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.62/0.57    inference(ennf_transformation,[],[f9])).
% 1.62/0.57  fof(f9,axiom,(
% 1.62/0.57    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.62/0.57    inference(definition_unfolding,[],[f21,f43])).
% 1.62/0.57  fof(f21,plain,(
% 1.62/0.57    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  fof(f13,plain,(
% 1.62/0.57    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 1.62/0.57    inference(flattening,[],[f12])).
% 1.62/0.57  fof(f12,plain,(
% 1.62/0.57    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f11])).
% 1.62/0.57  fof(f11,negated_conjecture,(
% 1.62/0.57    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 1.62/0.57    inference(negated_conjecture,[],[f10])).
% 1.62/0.57  fof(f10,conjecture,(
% 1.62/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).
% 1.62/0.57  fof(f223,plain,(
% 1.62/0.57    k1_xboole_0 != sK2 | spl10_8),
% 1.62/0.57    inference(avatar_component_clause,[],[f222])).
% 1.62/0.57  fof(f222,plain,(
% 1.62/0.57    spl10_8 <=> k1_xboole_0 = sK2),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.62/0.57  fof(f219,plain,(
% 1.62/0.57    k1_xboole_0 != sK3 | spl10_7),
% 1.62/0.57    inference(avatar_component_clause,[],[f218])).
% 1.62/0.57  fof(f218,plain,(
% 1.62/0.57    spl10_7 <=> k1_xboole_0 = sK3),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.62/0.57  fof(f215,plain,(
% 1.62/0.57    k1_xboole_0 != sK0 | spl10_6),
% 1.62/0.57    inference(avatar_component_clause,[],[f214])).
% 1.62/0.57  fof(f214,plain,(
% 1.62/0.57    spl10_6 <=> k1_xboole_0 = sK0),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.62/0.57  fof(f227,plain,(
% 1.62/0.57    k1_xboole_0 != sK1 | spl10_9),
% 1.62/0.57    inference(avatar_component_clause,[],[f226])).
% 1.62/0.57  fof(f226,plain,(
% 1.62/0.57    spl10_9 <=> k1_xboole_0 = sK1),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.62/0.57  fof(f117,plain,(
% 1.62/0.57    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | spl10_3),
% 1.62/0.57    inference(avatar_component_clause,[],[f115])).
% 1.62/0.57  fof(f115,plain,(
% 1.62/0.57    spl10_3 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.62/0.57  fof(f150,plain,(
% 1.62/0.57    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f74,f40])).
% 1.62/0.57  fof(f40,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f19])).
% 1.62/0.57  fof(f74,plain,(
% 1.62/0.57    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f44,f40])).
% 1.62/0.57  fof(f44,plain,(
% 1.62/0.57    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 1.62/0.57    inference(definition_unfolding,[],[f22,f43])).
% 1.62/0.57  fof(f22,plain,(
% 1.62/0.57    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  fof(f590,plain,(
% 1.62/0.57    spl10_2 | ~spl10_10),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f584])).
% 1.62/0.57  fof(f584,plain,(
% 1.62/0.57    $false | (spl10_2 | ~spl10_10)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f74,f581,f41])).
% 1.62/0.57  fof(f581,plain,(
% 1.62/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | (spl10_2 | ~spl10_10)),
% 1.62/0.57    inference(forward_demodulation,[],[f113,f281])).
% 1.62/0.57  fof(f281,plain,(
% 1.62/0.57    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | ~spl10_10),
% 1.62/0.57    inference(avatar_component_clause,[],[f279])).
% 1.62/0.57  fof(f279,plain,(
% 1.62/0.57    spl10_10 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.62/0.57  fof(f113,plain,(
% 1.62/0.57    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | spl10_2),
% 1.62/0.57    inference(avatar_component_clause,[],[f111])).
% 1.62/0.57  fof(f111,plain,(
% 1.62/0.57    spl10_2 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.62/0.57  fof(f579,plain,(
% 1.62/0.57    spl10_4 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f573])).
% 1.62/0.57  fof(f573,plain,(
% 1.62/0.57    $false | (spl10_4 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f150,f570,f40])).
% 1.62/0.57  fof(f570,plain,(
% 1.62/0.57    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | (spl10_4 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 1.62/0.57    inference(backward_demodulation,[],[f121,f562])).
% 1.62/0.57  fof(f562,plain,(
% 1.62/0.57    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f227,f215,f219,f223,f45,f49])).
% 1.62/0.57  fof(f49,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f27,f43])).
% 1.62/0.57  fof(f27,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f14])).
% 1.62/0.57  fof(f121,plain,(
% 1.62/0.57    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | spl10_4),
% 1.62/0.57    inference(avatar_component_clause,[],[f119])).
% 1.62/0.57  fof(f119,plain,(
% 1.62/0.57    spl10_4 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.62/0.57  fof(f544,plain,(
% 1.62/0.57    ~spl10_9),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f540])).
% 1.62/0.57  fof(f540,plain,(
% 1.62/0.57    $false | ~spl10_9),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f39,f460,f38])).
% 1.62/0.57  fof(f38,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f3])).
% 1.62/0.57  fof(f3,axiom,(
% 1.62/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.57  fof(f460,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) | ~spl10_9),
% 1.62/0.57    inference(backward_demodulation,[],[f242,f228])).
% 1.62/0.57  fof(f228,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | ~spl10_9),
% 1.62/0.57    inference(avatar_component_clause,[],[f226])).
% 1.62/0.57  fof(f242,plain,(
% 1.62/0.57    ~r1_tarski(sK1,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f197,f32])).
% 1.62/0.57  fof(f32,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f17])).
% 1.62/0.57  fof(f17,plain,(
% 1.62/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.62/0.57    inference(ennf_transformation,[],[f5])).
% 1.62/0.57  fof(f5,axiom,(
% 1.62/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.62/0.57  fof(f197,plain,(
% 1.62/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK1)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f62,f183,f33])).
% 1.62/0.57  fof(f33,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f18])).
% 1.62/0.57  fof(f18,plain,(
% 1.62/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f1])).
% 1.62/0.57  fof(f1,axiom,(
% 1.62/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.57  fof(f183,plain,(
% 1.62/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f150,f41])).
% 1.62/0.57  fof(f62,plain,(
% 1.62/0.57    r1_tarski(sK5,sK1)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f25,f38])).
% 1.62/0.57  fof(f25,plain,(
% 1.62/0.57    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  fof(f39,plain,(
% 1.62/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f2])).
% 1.62/0.57  fof(f2,axiom,(
% 1.62/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.62/0.57  fof(f450,plain,(
% 1.62/0.57    ~spl10_8),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f446])).
% 1.62/0.57  fof(f446,plain,(
% 1.62/0.57    $false | ~spl10_8),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f39,f393,f38])).
% 1.62/0.57  fof(f393,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(sK8))) | ~spl10_8),
% 1.62/0.57    inference(backward_demodulation,[],[f163,f224])).
% 1.62/0.57  fof(f224,plain,(
% 1.62/0.57    k1_xboole_0 = sK2 | ~spl10_8),
% 1.62/0.57    inference(avatar_component_clause,[],[f222])).
% 1.62/0.57  fof(f163,plain,(
% 1.62/0.57    ~r1_tarski(sK2,k2_mcart_1(k1_mcart_1(sK8)))),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f158,f32])).
% 1.62/0.57  fof(f158,plain,(
% 1.62/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f53,f151,f33])).
% 1.62/0.57  fof(f151,plain,(
% 1.62/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f74,f41])).
% 1.62/0.57  fof(f53,plain,(
% 1.62/0.57    r1_tarski(sK6,sK2)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f24,f38])).
% 1.62/0.57  fof(f24,plain,(
% 1.62/0.57    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  fof(f384,plain,(
% 1.62/0.57    ~spl10_7),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f380])).
% 1.62/0.57  fof(f380,plain,(
% 1.62/0.57    $false | ~spl10_7),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f39,f328,f38])).
% 1.62/0.57  fof(f328,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,k2_mcart_1(sK8)) | ~spl10_7),
% 1.62/0.57    inference(backward_demodulation,[],[f87,f220])).
% 1.62/0.57  fof(f220,plain,(
% 1.62/0.57    k1_xboole_0 = sK3 | ~spl10_7),
% 1.62/0.57    inference(avatar_component_clause,[],[f218])).
% 1.62/0.57  fof(f87,plain,(
% 1.62/0.57    ~r1_tarski(sK3,k2_mcart_1(sK8))),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f82,f32])).
% 1.62/0.57  fof(f82,plain,(
% 1.62/0.57    r2_hidden(k2_mcart_1(sK8),sK3)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f50,f75,f33])).
% 1.62/0.57  fof(f75,plain,(
% 1.62/0.57    r2_hidden(k2_mcart_1(sK8),sK7)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f44,f41])).
% 1.62/0.57  fof(f50,plain,(
% 1.62/0.57    r1_tarski(sK7,sK3)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f23,f38])).
% 1.62/0.57  fof(f23,plain,(
% 1.62/0.57    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  fof(f320,plain,(
% 1.62/0.57    ~spl10_6),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f316])).
% 1.62/0.57  fof(f316,plain,(
% 1.62/0.57    $false | ~spl10_6),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f39,f291,f38])).
% 1.62/0.57  fof(f291,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) | ~spl10_6),
% 1.62/0.57    inference(backward_demodulation,[],[f202,f216])).
% 1.62/0.57  fof(f216,plain,(
% 1.62/0.57    k1_xboole_0 = sK0 | ~spl10_6),
% 1.62/0.57    inference(avatar_component_clause,[],[f214])).
% 1.62/0.57  fof(f202,plain,(
% 1.62/0.57    ~r1_tarski(sK0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f191,f32])).
% 1.62/0.57  fof(f191,plain,(
% 1.62/0.57    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK0)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f65,f182,f33])).
% 1.62/0.57  fof(f182,plain,(
% 1.62/0.57    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f150,f40])).
% 1.62/0.57  fof(f65,plain,(
% 1.62/0.57    r1_tarski(sK4,sK0)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f26,f38])).
% 1.62/0.57  fof(f26,plain,(
% 1.62/0.57    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  fof(f282,plain,(
% 1.62/0.57    spl10_10 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 1.62/0.57    inference(avatar_split_clause,[],[f100,f226,f222,f218,f214,f279])).
% 1.62/0.57  fof(f100,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 1.62/0.57    inference(resolution,[],[f45,f47])).
% 1.62/0.57  fof(f47,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f29,f43])).
% 1.62/0.57  fof(f29,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f14])).
% 1.62/0.57  fof(f240,plain,(
% 1.62/0.57    spl10_1 | ~spl10_5),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f233])).
% 1.62/0.57  fof(f233,plain,(
% 1.62/0.57    $false | (spl10_1 | ~spl10_5)),
% 1.62/0.57    inference(unit_resulting_resolution,[],[f44,f230,f41])).
% 1.62/0.57  fof(f230,plain,(
% 1.62/0.57    ~r2_hidden(k2_mcart_1(sK8),sK7) | (spl10_1 | ~spl10_5)),
% 1.62/0.57    inference(backward_demodulation,[],[f109,f212])).
% 1.62/0.57  fof(f212,plain,(
% 1.62/0.57    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl10_5),
% 1.62/0.57    inference(avatar_component_clause,[],[f210])).
% 1.62/0.57  fof(f210,plain,(
% 1.62/0.57    spl10_5 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.62/0.57  fof(f109,plain,(
% 1.62/0.57    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | spl10_1),
% 1.62/0.57    inference(avatar_component_clause,[],[f107])).
% 1.62/0.57  fof(f107,plain,(
% 1.62/0.57    spl10_1 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.62/0.57  fof(f229,plain,(
% 1.62/0.57    spl10_5 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 1.62/0.57    inference(avatar_split_clause,[],[f101,f226,f222,f218,f214,f210])).
% 1.62/0.57  fof(f101,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 1.62/0.57    inference(resolution,[],[f45,f46])).
% 1.62/0.57  fof(f46,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f30,f43])).
% 1.62/0.57  fof(f30,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f14])).
% 1.62/0.57  fof(f122,plain,(
% 1.62/0.57    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 1.62/0.57    inference(avatar_split_clause,[],[f20,f119,f115,f111,f107])).
% 1.62/0.57  fof(f20,plain,(
% 1.62/0.57    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 1.62/0.57    inference(cnf_transformation,[],[f13])).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (28081)------------------------------
% 1.62/0.57  % (28081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (28081)Termination reason: Refutation
% 1.62/0.57  % (28099)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.62/0.58  
% 1.62/0.58  % (28081)Memory used [KB]: 6524
% 1.62/0.58  % (28081)Time elapsed: 0.159 s
% 1.62/0.58  % (28081)------------------------------
% 1.62/0.58  % (28081)------------------------------
% 1.62/0.58  % (28075)Success in time 0.216 s
%------------------------------------------------------------------------------
