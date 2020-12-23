%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 490 expanded)
%              Number of leaves         :   19 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  331 (1652 expanded)
%              Number of equality atoms :   89 ( 249 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f719,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f201,f214,f263,f366,f435,f501,f644,f692,f705,f718])).

fof(f718,plain,
    ( spl10_3
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | spl10_3
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f140,f706,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f706,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | spl10_3
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(forward_demodulation,[],[f113,f673])).

fof(f673,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f199,f187,f191,f195,f41,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f41,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f18,f39])).

fof(f18,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f195,plain,
    ( k1_xboole_0 != sK2
    | spl10_8 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl10_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f191,plain,
    ( k1_xboole_0 != sK3
    | spl10_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl10_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f187,plain,
    ( k1_xboole_0 != sK0
    | spl10_6 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl10_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f199,plain,
    ( k1_xboole_0 != sK1
    | spl10_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f113,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_3
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f140,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f75,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(unit_resulting_resolution,[],[f40,f28])).

fof(f40,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f19,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f705,plain,
    ( spl10_2
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | spl10_2
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f75,f694,f29])).

fof(f694,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | spl10_2
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f109,f262])).

fof(f262,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl10_10
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f109,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_2
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f692,plain,
    ( spl10_4
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | spl10_4
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f140,f680,f28])).

fof(f680,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | spl10_4
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(backward_demodulation,[],[f117,f672])).

fof(f672,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(unit_resulting_resolution,[],[f199,f187,f191,f195,f41,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f117,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_4
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f644,plain,(
    ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f38,f512,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f512,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),k1_xboole_0)
    | ~ spl10_9 ),
    inference(backward_demodulation,[],[f236,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f236,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK1) ),
    inference(unit_resulting_resolution,[],[f63,f229,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f229,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(unit_resulting_resolution,[],[f140,f29])).

fof(f63,plain,(
    r1_tarski(sK5,sK1) ),
    inference(unit_resulting_resolution,[],[f22,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f22,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f501,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f38,f444,f30])).

fof(f444,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),k1_xboole_0)
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f144,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f194])).

fof(f144,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2) ),
    inference(unit_resulting_resolution,[],[f48,f141,f31])).

fof(f141,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(unit_resulting_resolution,[],[f75,f29])).

fof(f48,plain,(
    r1_tarski(sK6,sK2) ),
    inference(unit_resulting_resolution,[],[f21,f36])).

fof(f21,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f435,plain,(
    ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f158,f159,f369,f31])).

fof(f369,plain,
    ( r1_tarski(sK7,k1_xboole_0)
    | ~ spl10_7 ),
    inference(backward_demodulation,[],[f46,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f46,plain,(
    r1_tarski(sK7,sK3) ),
    inference(unit_resulting_resolution,[],[f20,f36])).

fof(f20,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f159,plain,(
    ~ r2_hidden(sK9(sK7,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f154,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,(
    ~ r1_tarski(sK7,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f93,f137,f31])).

fof(f137,plain,(
    ~ r2_hidden(sK9(sK7,k2_mcart_1(sK8)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f38,f94,f31])).

fof(f94,plain,(
    ~ r2_hidden(sK9(sK7,k2_mcart_1(sK8)),k2_mcart_1(sK8)) ),
    inference(unit_resulting_resolution,[],[f86,f33])).

fof(f86,plain,(
    ~ r1_tarski(sK7,k2_mcart_1(sK8)) ),
    inference(unit_resulting_resolution,[],[f76,f30])).

fof(f76,plain,(
    r2_hidden(k2_mcart_1(sK8),sK7) ),
    inference(unit_resulting_resolution,[],[f40,f29])).

fof(f93,plain,(
    r2_hidden(sK9(sK7,k2_mcart_1(sK8)),sK7) ),
    inference(unit_resulting_resolution,[],[f86,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f158,plain,(
    r2_hidden(sK9(sK7,k1_xboole_0),sK7) ),
    inference(unit_resulting_resolution,[],[f154,f32])).

fof(f366,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f38,f274,f30])).

fof(f274,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),k1_xboole_0)
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f232,f188])).

fof(f188,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f186])).

fof(f232,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK0) ),
    inference(unit_resulting_resolution,[],[f73,f228,f31])).

fof(f228,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    inference(unit_resulting_resolution,[],[f140,f28])).

fof(f73,plain,(
    r1_tarski(sK4,sK0) ),
    inference(unit_resulting_resolution,[],[f23,f36])).

fof(f23,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f263,plain,
    ( spl10_10
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f90,f198,f194,f190,f186,f260])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f214,plain,
    ( spl10_1
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl10_1
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f40,f203,f29])).

fof(f203,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | spl10_1
    | ~ spl10_5 ),
    inference(backward_demodulation,[],[f105,f184])).

fof(f184,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl10_5
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f105,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_1
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f201,plain,
    ( spl10_5
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f91,f198,f194,f190,f186,f182])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f118,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f17,f115,f111,f107,f103])).

fof(f17,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:06:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (5987)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (5998)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (5989)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (6005)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (5982)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (5990)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (5981)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (5976)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (5991)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (5980)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (5999)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (5977)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (5997)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (5979)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (5993)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (5988)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (5978)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (6000)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (5994)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (5996)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (6003)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (5983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (5985)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (5984)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (5986)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (5995)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (5992)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (6001)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (6004)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (6002)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.58  % (5980)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f719,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f118,f201,f214,f263,f366,f435,f501,f644,f692,f705,f718])).
% 0.22/0.59  fof(f718,plain,(
% 0.22/0.59    spl10_3 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f710])).
% 0.22/0.59  fof(f710,plain,(
% 0.22/0.59    $false | (spl10_3 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f140,f706,f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.59  fof(f706,plain,(
% 0.22/0.59    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | (spl10_3 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 0.22/0.59    inference(forward_demodulation,[],[f113,f673])).
% 0.22/0.59  fof(f673,plain,(
% 0.22/0.59    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f199,f187,f191,f195,f41,f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f25,f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f34,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.22/0.59    inference(definition_unfolding,[],[f18,f39])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(flattening,[],[f11])).
% 0.22/0.59  fof(f11,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.22/0.59    inference(negated_conjecture,[],[f9])).
% 0.22/0.59  fof(f9,conjecture,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).
% 0.22/0.59  fof(f195,plain,(
% 0.22/0.59    k1_xboole_0 != sK2 | spl10_8),
% 0.22/0.59    inference(avatar_component_clause,[],[f194])).
% 0.22/0.59  fof(f194,plain,(
% 0.22/0.59    spl10_8 <=> k1_xboole_0 = sK2),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.59  fof(f191,plain,(
% 0.22/0.59    k1_xboole_0 != sK3 | spl10_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f190])).
% 0.22/0.59  fof(f190,plain,(
% 0.22/0.59    spl10_7 <=> k1_xboole_0 = sK3),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.59  fof(f187,plain,(
% 0.22/0.59    k1_xboole_0 != sK0 | spl10_6),
% 0.22/0.59    inference(avatar_component_clause,[],[f186])).
% 0.22/0.59  fof(f186,plain,(
% 0.22/0.59    spl10_6 <=> k1_xboole_0 = sK0),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.59  fof(f199,plain,(
% 0.22/0.59    k1_xboole_0 != sK1 | spl10_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f198])).
% 0.22/0.59  fof(f198,plain,(
% 0.22/0.59    spl10_9 <=> k1_xboole_0 = sK1),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | spl10_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f111])).
% 0.22/0.59  fof(f111,plain,(
% 0.22/0.59    spl10_3 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.59  fof(f140,plain,(
% 0.22/0.59    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f75,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f40,f28])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.59    inference(definition_unfolding,[],[f19,f39])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f705,plain,(
% 0.22/0.59    spl10_2 | ~spl10_10),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f697])).
% 0.22/0.59  fof(f697,plain,(
% 0.22/0.59    $false | (spl10_2 | ~spl10_10)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f75,f694,f29])).
% 0.22/0.59  fof(f694,plain,(
% 0.22/0.59    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | (spl10_2 | ~spl10_10)),
% 0.22/0.59    inference(forward_demodulation,[],[f109,f262])).
% 0.22/0.59  fof(f262,plain,(
% 0.22/0.59    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | ~spl10_10),
% 0.22/0.59    inference(avatar_component_clause,[],[f260])).
% 0.22/0.59  fof(f260,plain,(
% 0.22/0.59    spl10_10 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.59  fof(f109,plain,(
% 0.22/0.59    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | spl10_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f107])).
% 0.22/0.59  fof(f107,plain,(
% 0.22/0.59    spl10_2 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.59  fof(f692,plain,(
% 0.22/0.59    spl10_4 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f684])).
% 0.22/0.59  fof(f684,plain,(
% 0.22/0.59    $false | (spl10_4 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f140,f680,f28])).
% 0.22/0.59  fof(f680,plain,(
% 0.22/0.59    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | (spl10_4 | spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 0.22/0.59    inference(backward_demodulation,[],[f117,f672])).
% 0.22/0.59  fof(f672,plain,(
% 0.22/0.59    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_6 | spl10_7 | spl10_8 | spl10_9)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f199,f187,f191,f195,f41,f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f24,f39])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f13])).
% 0.22/0.59  fof(f117,plain,(
% 0.22/0.59    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | spl10_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f115])).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    spl10_4 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.59  fof(f644,plain,(
% 0.22/0.59    ~spl10_9),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f643])).
% 0.22/0.59  fof(f643,plain,(
% 0.22/0.59    $false | ~spl10_9),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f38,f512,f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.59  fof(f512,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),k1_xboole_0) | ~spl10_9),
% 0.22/0.59    inference(backward_demodulation,[],[f236,f200])).
% 0.22/0.59  fof(f200,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~spl10_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f198])).
% 0.22/0.59  fof(f236,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK1)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f63,f229,f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.59  fof(f229,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f140,f29])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    r1_tarski(sK5,sK1)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f22,f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.59  fof(f501,plain,(
% 0.22/0.59    ~spl10_8),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f500])).
% 0.22/0.59  fof(f500,plain,(
% 0.22/0.59    $false | ~spl10_8),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f38,f444,f30])).
% 0.22/0.59  fof(f444,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),k1_xboole_0) | ~spl10_8),
% 0.22/0.59    inference(backward_demodulation,[],[f144,f196])).
% 0.22/0.59  fof(f196,plain,(
% 0.22/0.59    k1_xboole_0 = sK2 | ~spl10_8),
% 0.22/0.59    inference(avatar_component_clause,[],[f194])).
% 0.22/0.59  fof(f144,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f48,f141,f31])).
% 0.22/0.59  fof(f141,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f75,f29])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    r1_tarski(sK6,sK2)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f21,f36])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f435,plain,(
% 0.22/0.59    ~spl10_7),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f425])).
% 0.22/0.59  fof(f425,plain,(
% 0.22/0.59    $false | ~spl10_7),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f158,f159,f369,f31])).
% 0.22/0.59  fof(f369,plain,(
% 0.22/0.59    r1_tarski(sK7,k1_xboole_0) | ~spl10_7),
% 0.22/0.59    inference(backward_demodulation,[],[f46,f192])).
% 0.22/0.59  fof(f192,plain,(
% 0.22/0.59    k1_xboole_0 = sK3 | ~spl10_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f190])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    r1_tarski(sK7,sK3)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f20,f36])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f159,plain,(
% 0.22/0.59    ~r2_hidden(sK9(sK7,k1_xboole_0),k1_xboole_0)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f154,f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f154,plain,(
% 0.22/0.59    ~r1_tarski(sK7,k1_xboole_0)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f93,f137,f31])).
% 0.22/0.59  fof(f137,plain,(
% 0.22/0.59    ~r2_hidden(sK9(sK7,k2_mcart_1(sK8)),k1_xboole_0)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f38,f94,f31])).
% 0.22/0.59  fof(f94,plain,(
% 0.22/0.59    ~r2_hidden(sK9(sK7,k2_mcart_1(sK8)),k2_mcart_1(sK8))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f86,f33])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ~r1_tarski(sK7,k2_mcart_1(sK8))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f76,f30])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    r2_hidden(k2_mcart_1(sK8),sK7)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f40,f29])).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    r2_hidden(sK9(sK7,k2_mcart_1(sK8)),sK7)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f86,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f158,plain,(
% 0.22/0.59    r2_hidden(sK9(sK7,k1_xboole_0),sK7)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f154,f32])).
% 0.22/0.59  fof(f366,plain,(
% 0.22/0.59    ~spl10_6),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f365])).
% 0.22/0.59  fof(f365,plain,(
% 0.22/0.59    $false | ~spl10_6),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f38,f274,f30])).
% 0.22/0.59  fof(f274,plain,(
% 0.22/0.59    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),k1_xboole_0) | ~spl10_6),
% 0.22/0.59    inference(backward_demodulation,[],[f232,f188])).
% 0.22/0.59  fof(f188,plain,(
% 0.22/0.59    k1_xboole_0 = sK0 | ~spl10_6),
% 0.22/0.59    inference(avatar_component_clause,[],[f186])).
% 0.22/0.59  fof(f232,plain,(
% 0.22/0.59    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK0)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f73,f228,f31])).
% 0.22/0.59  fof(f228,plain,(
% 0.22/0.59    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f140,f28])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    r1_tarski(sK4,sK0)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f23,f36])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f263,plain,(
% 0.22/0.59    spl10_10 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 0.22/0.59    inference(avatar_split_clause,[],[f90,f198,f194,f190,f186,f260])).
% 0.22/0.59  fof(f90,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 0.22/0.59    inference(resolution,[],[f41,f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f26,f39])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f13])).
% 0.22/0.59  fof(f214,plain,(
% 0.22/0.59    spl10_1 | ~spl10_5),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f206])).
% 0.22/0.59  fof(f206,plain,(
% 0.22/0.59    $false | (spl10_1 | ~spl10_5)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f40,f203,f29])).
% 0.22/0.59  fof(f203,plain,(
% 0.22/0.59    ~r2_hidden(k2_mcart_1(sK8),sK7) | (spl10_1 | ~spl10_5)),
% 0.22/0.59    inference(backward_demodulation,[],[f105,f184])).
% 0.22/0.59  fof(f184,plain,(
% 0.22/0.59    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl10_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f182])).
% 0.22/0.59  fof(f182,plain,(
% 0.22/0.59    spl10_5 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | spl10_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f103])).
% 0.22/0.59  fof(f103,plain,(
% 0.22/0.59    spl10_1 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.59  fof(f201,plain,(
% 0.22/0.59    spl10_5 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 0.22/0.59    inference(avatar_split_clause,[],[f91,f198,f194,f190,f186,f182])).
% 0.22/0.59  fof(f91,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 0.22/0.59    inference(resolution,[],[f41,f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f27,f39])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f13])).
% 0.22/0.59  fof(f118,plain,(
% 0.22/0.59    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f17,f115,f111,f107,f103])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (5980)------------------------------
% 0.22/0.59  % (5980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (5980)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (5980)Memory used [KB]: 6524
% 0.22/0.59  % (5980)Time elapsed: 0.142 s
% 0.22/0.59  % (5980)------------------------------
% 0.22/0.59  % (5980)------------------------------
% 0.22/0.59  % (5975)Success in time 0.223 s
%------------------------------------------------------------------------------
