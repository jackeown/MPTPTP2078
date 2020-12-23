%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:40 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 241 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  237 ( 836 expanded)
%              Number of equality atoms :   60 ( 117 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f142,f159,f191,f216,f244,f273,f325,f344])).

fof(f344,plain,
    ( spl8_2
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl8_2
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f55,f333,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f333,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl8_2
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(backward_demodulation,[],[f77,f328])).

fof(f328,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f140,f132,f136,f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f42,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f21,f35])).

fof(f21,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f136,plain,
    ( k1_xboole_0 != sK2
    | spl8_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f132,plain,
    ( k1_xboole_0 != sK0
    | spl8_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f140,plain,
    ( k1_xboole_0 != sK1
    | spl8_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f77,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f55,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f22,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f325,plain,
    ( spl8_3
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl8_3
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f55,f274,f30])).

fof(f274,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl8_3
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f81,f190])).

fof(f190,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_8
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f81,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_3
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f273,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f39,f38,f250,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f250,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f101,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f101,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f24,f87,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f87,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(unit_resulting_resolution,[],[f55,f31])).

fof(f24,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f244,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f39,f38,f221,f40])).

fof(f221,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f61,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f23,f56,f29])).

fof(f56,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(unit_resulting_resolution,[],[f41,f31])).

fof(f23,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f216,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f39,f38,f197,f40])).

fof(f197,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f89,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f89,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f25,f86,f29])).

fof(f86,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(unit_resulting_resolution,[],[f55,f30])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f191,plain,
    ( spl8_8
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f57,f139,f135,f131,f188])).

fof(f57,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f159,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f41,f147,f31])).

fof(f147,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl8_1
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f73,f129])).

fof(f129,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_4
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f73,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_1
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f142,plain,
    ( spl8_4
    | spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f59,f139,f135,f131,f127])).

fof(f59,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f20,f79,f75,f71])).

fof(f20,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (24503)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (24495)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (24506)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (24487)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.51  % (24485)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.51  % (24486)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.52  % (24491)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.52  % (24498)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  % (24490)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.52  % (24480)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.52  % (24492)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (24482)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (24484)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.53  % (24508)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.53  % (24481)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.53  % (24507)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.53  % (24509)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.54  % (24493)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.54  % (24496)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.54  % (24500)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.54  % (24499)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  % (24489)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (24497)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.54  % (24488)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.54  % (24484)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f345,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f82,f142,f159,f191,f216,f244,f273,f325,f344])).
% 1.37/0.54  fof(f344,plain,(
% 1.37/0.54    spl8_2 | spl8_5 | spl8_6 | spl8_7),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f336])).
% 1.37/0.54  fof(f336,plain,(
% 1.37/0.54    $false | (spl8_2 | spl8_5 | spl8_6 | spl8_7)),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f55,f333,f31])).
% 1.37/0.55  fof(f31,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f16])).
% 1.37/0.55  fof(f16,plain,(
% 1.37/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.37/0.55    inference(ennf_transformation,[],[f8])).
% 1.37/0.55  fof(f8,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.37/0.55  fof(f333,plain,(
% 1.37/0.55    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl8_2 | spl8_5 | spl8_6 | spl8_7)),
% 1.37/0.55    inference(backward_demodulation,[],[f77,f328])).
% 1.37/0.55  fof(f328,plain,(
% 1.37/0.55    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | (spl8_5 | spl8_6 | spl8_7)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f140,f132,f136,f42,f44])).
% 1.37/0.55  fof(f44,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.37/0.55    inference(definition_unfolding,[],[f27,f35])).
% 1.37/0.55  fof(f35,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f7])).
% 1.37/0.55  fof(f7,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.37/0.55  fof(f27,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f14])).
% 1.37/0.55  fof(f14,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.37/0.55  fof(f42,plain,(
% 1.37/0.55    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.37/0.55    inference(definition_unfolding,[],[f21,f35])).
% 1.37/0.55  fof(f21,plain,(
% 1.37/0.55    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.37/0.55    inference(cnf_transformation,[],[f13])).
% 1.37/0.55  fof(f13,plain,(
% 1.37/0.55    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.37/0.55    inference(flattening,[],[f12])).
% 1.37/0.55  fof(f12,plain,(
% 1.37/0.55    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f11])).
% 1.37/0.55  fof(f11,negated_conjecture,(
% 1.37/0.55    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.37/0.55    inference(negated_conjecture,[],[f10])).
% 1.37/0.55  fof(f10,conjecture,(
% 1.37/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).
% 1.37/0.55  fof(f136,plain,(
% 1.37/0.55    k1_xboole_0 != sK2 | spl8_6),
% 1.37/0.55    inference(avatar_component_clause,[],[f135])).
% 1.37/0.55  fof(f135,plain,(
% 1.37/0.55    spl8_6 <=> k1_xboole_0 = sK2),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.37/0.55  fof(f132,plain,(
% 1.37/0.55    k1_xboole_0 != sK0 | spl8_5),
% 1.37/0.55    inference(avatar_component_clause,[],[f131])).
% 1.37/0.55  fof(f131,plain,(
% 1.37/0.55    spl8_5 <=> k1_xboole_0 = sK0),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.37/0.55  fof(f140,plain,(
% 1.37/0.55    k1_xboole_0 != sK1 | spl8_7),
% 1.37/0.55    inference(avatar_component_clause,[],[f139])).
% 1.37/0.55  fof(f139,plain,(
% 1.37/0.55    spl8_7 <=> k1_xboole_0 = sK1),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.37/0.55  fof(f77,plain,(
% 1.37/0.55    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl8_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f75])).
% 1.37/0.55  fof(f75,plain,(
% 1.37/0.55    spl8_2 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.37/0.55  fof(f55,plain,(
% 1.37/0.55    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f41,f30])).
% 1.37/0.55  fof(f30,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f16])).
% 1.37/0.55  fof(f41,plain,(
% 1.37/0.55    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.37/0.55    inference(definition_unfolding,[],[f22,f35])).
% 1.37/0.55  fof(f22,plain,(
% 1.37/0.55    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.37/0.55    inference(cnf_transformation,[],[f13])).
% 1.37/0.55  fof(f325,plain,(
% 1.37/0.55    spl8_3 | ~spl8_8),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f317])).
% 1.37/0.55  fof(f317,plain,(
% 1.37/0.55    $false | (spl8_3 | ~spl8_8)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f55,f274,f30])).
% 1.37/0.55  fof(f274,plain,(
% 1.37/0.55    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (spl8_3 | ~spl8_8)),
% 1.37/0.55    inference(backward_demodulation,[],[f81,f190])).
% 1.37/0.55  fof(f190,plain,(
% 1.37/0.55    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl8_8),
% 1.37/0.55    inference(avatar_component_clause,[],[f188])).
% 1.37/0.55  fof(f188,plain,(
% 1.37/0.55    spl8_8 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.37/0.55  fof(f81,plain,(
% 1.37/0.55    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl8_3),
% 1.37/0.55    inference(avatar_component_clause,[],[f79])).
% 1.37/0.55  fof(f79,plain,(
% 1.37/0.55    spl8_3 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.37/0.55  fof(f273,plain,(
% 1.37/0.55    ~spl8_7),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f271])).
% 1.37/0.55  fof(f271,plain,(
% 1.37/0.55    $false | ~spl8_7),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f39,f38,f250,f40])).
% 1.37/0.55  fof(f40,plain,(
% 1.37/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f19])).
% 1.37/0.55  fof(f19,plain,(
% 1.37/0.55    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.37/0.55    inference(flattening,[],[f18])).
% 1.37/0.55  fof(f18,plain,(
% 1.37/0.55    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.37/0.55    inference(ennf_transformation,[],[f4])).
% 1.37/0.55  fof(f4,axiom,(
% 1.37/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.37/0.55  fof(f250,plain,(
% 1.37/0.55    ~v1_xboole_0(k1_xboole_0) | ~spl8_7),
% 1.37/0.55    inference(backward_demodulation,[],[f101,f141])).
% 1.37/0.55  fof(f141,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | ~spl8_7),
% 1.37/0.55    inference(avatar_component_clause,[],[f139])).
% 1.37/0.55  fof(f101,plain,(
% 1.37/0.55    ~v1_xboole_0(sK1)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f24,f87,f29])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f15])).
% 1.37/0.55  fof(f15,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.37/0.55    inference(ennf_transformation,[],[f6])).
% 1.37/0.55  fof(f6,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.37/0.55  fof(f87,plain,(
% 1.37/0.55    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f55,f31])).
% 1.37/0.55  fof(f24,plain,(
% 1.37/0.55    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 1.37/0.55    inference(cnf_transformation,[],[f13])).
% 1.37/0.55  fof(f38,plain,(
% 1.37/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f2])).
% 1.37/0.55  fof(f2,axiom,(
% 1.37/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.37/0.55  fof(f39,plain,(
% 1.37/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f3])).
% 1.37/0.55  fof(f3,axiom,(
% 1.37/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.37/0.55  fof(f244,plain,(
% 1.37/0.55    ~spl8_6),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f242])).
% 1.37/0.55  fof(f242,plain,(
% 1.37/0.55    $false | ~spl8_6),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f39,f38,f221,f40])).
% 1.37/0.55  fof(f221,plain,(
% 1.37/0.55    ~v1_xboole_0(k1_xboole_0) | ~spl8_6),
% 1.37/0.55    inference(backward_demodulation,[],[f61,f137])).
% 1.37/0.55  fof(f137,plain,(
% 1.37/0.55    k1_xboole_0 = sK2 | ~spl8_6),
% 1.37/0.55    inference(avatar_component_clause,[],[f135])).
% 1.37/0.55  fof(f61,plain,(
% 1.37/0.55    ~v1_xboole_0(sK2)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f23,f56,f29])).
% 1.37/0.55  fof(f56,plain,(
% 1.37/0.55    r2_hidden(k2_mcart_1(sK6),sK5)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f41,f31])).
% 1.37/0.55  fof(f23,plain,(
% 1.37/0.55    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 1.37/0.55    inference(cnf_transformation,[],[f13])).
% 1.37/0.55  fof(f216,plain,(
% 1.37/0.55    ~spl8_5),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f214])).
% 1.37/0.55  fof(f214,plain,(
% 1.37/0.55    $false | ~spl8_5),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f39,f38,f197,f40])).
% 1.37/0.55  fof(f197,plain,(
% 1.37/0.55    ~v1_xboole_0(k1_xboole_0) | ~spl8_5),
% 1.37/0.55    inference(backward_demodulation,[],[f89,f133])).
% 1.37/0.55  fof(f133,plain,(
% 1.37/0.55    k1_xboole_0 = sK0 | ~spl8_5),
% 1.37/0.55    inference(avatar_component_clause,[],[f131])).
% 1.37/0.55  fof(f89,plain,(
% 1.37/0.55    ~v1_xboole_0(sK0)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f25,f86,f29])).
% 1.37/0.55  fof(f86,plain,(
% 1.37/0.55    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f55,f30])).
% 1.37/0.55  fof(f25,plain,(
% 1.37/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.37/0.55    inference(cnf_transformation,[],[f13])).
% 1.37/0.55  fof(f191,plain,(
% 1.37/0.55    spl8_8 | spl8_5 | spl8_6 | spl8_7),
% 1.37/0.55    inference(avatar_split_clause,[],[f57,f139,f135,f131,f188])).
% 1.37/0.55  fof(f57,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 1.37/0.55    inference(resolution,[],[f42,f45])).
% 1.37/0.55  fof(f45,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.37/0.55    inference(definition_unfolding,[],[f26,f35])).
% 1.37/0.55  fof(f26,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f14])).
% 1.37/0.55  fof(f159,plain,(
% 1.37/0.55    spl8_1 | ~spl8_4),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f150])).
% 1.37/0.55  fof(f150,plain,(
% 1.37/0.55    $false | (spl8_1 | ~spl8_4)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f41,f147,f31])).
% 1.37/0.55  fof(f147,plain,(
% 1.37/0.55    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl8_1 | ~spl8_4)),
% 1.37/0.55    inference(backward_demodulation,[],[f73,f129])).
% 1.37/0.55  fof(f129,plain,(
% 1.37/0.55    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl8_4),
% 1.37/0.55    inference(avatar_component_clause,[],[f127])).
% 1.37/0.55  fof(f127,plain,(
% 1.37/0.55    spl8_4 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.37/0.55  fof(f73,plain,(
% 1.37/0.55    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl8_1),
% 1.37/0.55    inference(avatar_component_clause,[],[f71])).
% 1.37/0.55  fof(f71,plain,(
% 1.37/0.55    spl8_1 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.37/0.55  fof(f142,plain,(
% 1.37/0.55    spl8_4 | spl8_5 | spl8_6 | spl8_7),
% 1.37/0.55    inference(avatar_split_clause,[],[f59,f139,f135,f131,f127])).
% 1.37/0.55  fof(f59,plain,(
% 1.37/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 1.37/0.55    inference(resolution,[],[f42,f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.37/0.55    inference(definition_unfolding,[],[f28,f35])).
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f14])).
% 1.37/0.55  fof(f82,plain,(
% 1.37/0.55    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.37/0.55    inference(avatar_split_clause,[],[f20,f79,f75,f71])).
% 1.37/0.55  fof(f20,plain,(
% 1.37/0.55    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.37/0.55    inference(cnf_transformation,[],[f13])).
% 1.37/0.55  % SZS output end Proof for theBenchmark
% 1.37/0.55  % (24484)------------------------------
% 1.37/0.55  % (24484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (24484)Termination reason: Refutation
% 1.37/0.55  
% 1.37/0.55  % (24484)Memory used [KB]: 6396
% 1.37/0.55  % (24484)Time elapsed: 0.142 s
% 1.37/0.55  % (24484)------------------------------
% 1.37/0.55  % (24484)------------------------------
% 1.37/0.55  % (24479)Success in time 0.19 s
%------------------------------------------------------------------------------
