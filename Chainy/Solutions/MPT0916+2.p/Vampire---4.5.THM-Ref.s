%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0916+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 31.38s
% Output     : Refutation 31.38s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 366 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  371 (1164 expanded)
%              Number of equality atoms :  119 ( 229 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4474,f4862,f4944,f5077,f5144,f5148,f7640,f7790,f7928,f12152,f18466,f20967,f21264,f21316])).

fof(f21316,plain,
    ( spl125_16
    | spl125_18
    | spl125_20
    | spl125_24 ),
    inference(avatar_contradiction_clause,[],[f21315])).

fof(f21315,plain,
    ( $false
    | spl125_16
    | spl125_18
    | spl125_20
    | spl125_24 ),
    inference(subsumption_resolution,[],[f4202,f21314])).

fof(f21314,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl125_16
    | spl125_18
    | spl125_20
    | spl125_24 ),
    inference(forward_demodulation,[],[f5143,f21309])).

fof(f21309,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | spl125_16
    | spl125_18
    | spl125_20 ),
    inference(subsumption_resolution,[],[f21308,f4473])).

fof(f4473,plain,
    ( k1_xboole_0 != sK0
    | spl125_16 ),
    inference(avatar_component_clause,[],[f4471])).

fof(f4471,plain,
    ( spl125_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_16])])).

fof(f21308,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | spl125_18
    | spl125_20 ),
    inference(subsumption_resolution,[],[f21307,f4943])).

fof(f4943,plain,
    ( k1_xboole_0 != sK2
    | spl125_20 ),
    inference(avatar_component_clause,[],[f4941])).

fof(f4941,plain,
    ( spl125_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_20])])).

fof(f21307,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | spl125_18 ),
    inference(subsumption_resolution,[],[f21291,f4861])).

fof(f4861,plain,
    ( k1_xboole_0 != sK1
    | spl125_18 ),
    inference(avatar_component_clause,[],[f4859])).

fof(f4859,plain,
    ( spl125_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_18])])).

fof(f21291,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(resolution,[],[f2391,f2370])).

fof(f2370,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f1725,f1798])).

fof(f1798,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f1725,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1397])).

fof(f1397,plain,(
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
    inference(flattening,[],[f1396])).

fof(f1396,plain,(
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
    inference(ennf_transformation,[],[f1385])).

fof(f1385,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1384])).

fof(f1384,conjecture,(
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

fof(f2391,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f1748,f1798])).

fof(f1748,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f1406])).

fof(f1406,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1356])).

fof(f1356,axiom,(
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

fof(f5143,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl125_24 ),
    inference(avatar_component_clause,[],[f5141])).

fof(f5141,plain,
    ( spl125_24
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_24])])).

fof(f4202,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(resolution,[],[f3970,f1879])).

fof(f1879,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f1466])).

fof(f1466,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1316])).

fof(f1316,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f3970,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f1879,f2369])).

fof(f2369,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f1726,f1798])).

fof(f1726,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f1397])).

fof(f21264,plain,
    ( spl125_16
    | spl125_18
    | spl125_20
    | spl125_23 ),
    inference(avatar_contradiction_clause,[],[f21263])).

fof(f21263,plain,
    ( $false
    | spl125_16
    | spl125_18
    | spl125_20
    | spl125_23 ),
    inference(subsumption_resolution,[],[f21261,f4201])).

fof(f4201,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(resolution,[],[f3970,f1880])).

fof(f1880,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f1466])).

fof(f21261,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl125_16
    | spl125_18
    | spl125_20
    | spl125_23 ),
    inference(backward_demodulation,[],[f5139,f21260])).

fof(f21260,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl125_16
    | spl125_18
    | spl125_20 ),
    inference(subsumption_resolution,[],[f21259,f4473])).

fof(f21259,plain,
    ( k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl125_18
    | spl125_20 ),
    inference(subsumption_resolution,[],[f21258,f4943])).

fof(f21258,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl125_18 ),
    inference(subsumption_resolution,[],[f21242,f4861])).

fof(f21242,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(resolution,[],[f2390,f2370])).

fof(f2390,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f1749,f1798])).

fof(f1749,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f1406])).

fof(f5139,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl125_23 ),
    inference(avatar_component_clause,[],[f5137])).

fof(f5137,plain,
    ( spl125_23
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_23])])).

fof(f20967,plain,
    ( spl125_16
    | spl125_18
    | spl125_20
    | spl125_22 ),
    inference(avatar_contradiction_clause,[],[f20966])).

fof(f20966,plain,
    ( $false
    | spl125_16
    | spl125_18
    | spl125_20
    | spl125_22 ),
    inference(subsumption_resolution,[],[f4001,f20947])).

fof(f20947,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl125_16
    | spl125_18
    | spl125_20
    | spl125_22 ),
    inference(forward_demodulation,[],[f5135,f20942])).

fof(f20942,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | spl125_16
    | spl125_18
    | spl125_20 ),
    inference(subsumption_resolution,[],[f20941,f4473])).

fof(f20941,plain,
    ( k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | spl125_18
    | spl125_20 ),
    inference(subsumption_resolution,[],[f20940,f4943])).

fof(f20940,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | spl125_18 ),
    inference(subsumption_resolution,[],[f20924,f4861])).

fof(f20924,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    inference(resolution,[],[f2389,f2370])).

fof(f2389,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f1750,f1798])).

fof(f1750,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f1406])).

fof(f5135,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl125_22 ),
    inference(avatar_component_clause,[],[f5133])).

fof(f5133,plain,
    ( spl125_22
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_22])])).

fof(f4001,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(resolution,[],[f1880,f2369])).

fof(f18466,plain,(
    ~ spl125_31 ),
    inference(avatar_contradiction_clause,[],[f18465])).

fof(f18465,plain,
    ( $false
    | ~ spl125_31 ),
    inference(subsumption_resolution,[],[f2834,f7789])).

fof(f7789,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4)
    | ~ spl125_31 ),
    inference(avatar_component_clause,[],[f7788])).

fof(f7788,plain,
    ( spl125_31
  <=> ! [X1] : ~ r2_hidden(X1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_31])])).

fof(f2834,plain,(
    r2_hidden(sK122(sK4),sK4) ),
    inference(resolution,[],[f2347,f2820])).

fof(f2820,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f2811,f2334])).

fof(f2334,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1702])).

fof(f1702,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f296])).

fof(f296,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f2811,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f2335,f2740])).

fof(f2740,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(resolution,[],[f2328,f2369])).

fof(f2328,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1694])).

fof(f1694,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2335,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1703])).

fof(f1703,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f297])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f2347,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK122(X0),X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f12152,plain,(
    ~ spl125_19 ),
    inference(avatar_contradiction_clause,[],[f12151])).

fof(f12151,plain,
    ( $false
    | ~ spl125_19 ),
    inference(subsumption_resolution,[],[f12150,f2759])).

fof(f2759,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f1992,f2646])).

fof(f2646,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1982])).

fof(f1982,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1992,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f12150,plain,
    ( r2_hidden(sK6,k1_xboole_0)
    | ~ spl125_19 ),
    inference(forward_demodulation,[],[f12149,f2625])).

fof(f2625,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f2423])).

fof(f2423,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f1794,f1798])).

fof(f1794,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f1339])).

fof(f1339,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f12149,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0))
    | ~ spl125_19 ),
    inference(forward_demodulation,[],[f2369,f4939])).

fof(f4939,plain,
    ( k1_xboole_0 = sK5
    | ~ spl125_19 ),
    inference(avatar_component_clause,[],[f4937])).

fof(f4937,plain,
    ( spl125_19
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_19])])).

fof(f7928,plain,(
    ~ spl125_25 ),
    inference(avatar_contradiction_clause,[],[f7927])).

fof(f7927,plain,
    ( $false
    | ~ spl125_25 ),
    inference(resolution,[],[f5147,f2833])).

fof(f2833,plain,(
    r2_hidden(sK122(sK3),sK3) ),
    inference(resolution,[],[f2347,f2819])).

fof(f2819,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f2811,f2335])).

fof(f5147,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl125_25 ),
    inference(avatar_component_clause,[],[f5146])).

fof(f5146,plain,
    ( spl125_25
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_25])])).

fof(f7790,plain,
    ( ~ spl125_30
    | spl125_31 ),
    inference(avatar_split_clause,[],[f3606,f7788,f7637])).

fof(f7637,plain,
    ( spl125_30
  <=> r1_xboole_0(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_30])])).

fof(f3606,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK4)
      | ~ r1_xboole_0(sK4,sK1) ) ),
    inference(superposition,[],[f1935,f3452])).

fof(f3452,plain,(
    sK4 = k3_xboole_0(sK4,sK1) ),
    inference(superposition,[],[f2274,f3420])).

fof(f3420,plain,(
    sK1 = k2_xboole_0(sK4,sK1) ),
    inference(resolution,[],[f2230,f2861])).

fof(f2861,plain,(
    r1_tarski(sK4,sK1) ),
    inference(resolution,[],[f1804,f1728])).

fof(f1728,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f1397])).

fof(f1804,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2230,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f1636])).

fof(f1636,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2274,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1935,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1510])).

fof(f1510,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1392])).

fof(f1392,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f7640,plain,
    ( spl125_30
    | ~ spl125_17 ),
    inference(avatar_split_clause,[],[f3605,f4855,f7637])).

fof(f4855,plain,
    ( spl125_17
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_17])])).

fof(f3605,plain,
    ( k1_xboole_0 != sK4
    | r1_xboole_0(sK4,sK1) ),
    inference(superposition,[],[f1925,f3452])).

fof(f1925,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f5148,plain,
    ( ~ spl125_21
    | spl125_25 ),
    inference(avatar_split_clause,[],[f3555,f5146,f5074])).

fof(f5074,plain,
    ( spl125_21
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_21])])).

fof(f3555,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ r1_xboole_0(sK3,sK0) ) ),
    inference(superposition,[],[f1935,f3434])).

fof(f3434,plain,(
    sK3 = k3_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f2274,f3419])).

fof(f3419,plain,(
    sK0 = k2_xboole_0(sK3,sK0) ),
    inference(resolution,[],[f2230,f2860])).

fof(f2860,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f1804,f1729])).

fof(f1729,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f1397])).

fof(f5144,plain,
    ( ~ spl125_22
    | ~ spl125_23
    | ~ spl125_24 ),
    inference(avatar_split_clause,[],[f1724,f5141,f5137,f5133])).

fof(f1724,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f1397])).

fof(f5077,plain,
    ( spl125_21
    | ~ spl125_15 ),
    inference(avatar_split_clause,[],[f3554,f4467,f5074])).

fof(f4467,plain,
    ( spl125_15
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl125_15])])).

fof(f3554,plain,
    ( k1_xboole_0 != sK3
    | r1_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f1925,f3434])).

fof(f4944,plain,
    ( spl125_19
    | ~ spl125_20 ),
    inference(avatar_split_clause,[],[f3481,f4941,f4937])).

fof(f3481,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK5 ),
    inference(superposition,[],[f2229,f3421])).

fof(f3421,plain,(
    sK2 = k2_xboole_0(sK5,sK2) ),
    inference(resolution,[],[f2230,f2862])).

fof(f2862,plain,(
    r1_tarski(sK5,sK2) ),
    inference(resolution,[],[f1804,f1727])).

fof(f1727,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f1397])).

fof(f2229,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1635])).

fof(f1635,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f4862,plain,
    ( spl125_17
    | ~ spl125_18 ),
    inference(avatar_split_clause,[],[f3447,f4859,f4855])).

fof(f3447,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f2229,f3420])).

fof(f4474,plain,
    ( spl125_15
    | ~ spl125_16 ),
    inference(avatar_split_clause,[],[f3429,f4471,f4467])).

fof(f3429,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f2229,f3419])).
%------------------------------------------------------------------------------
