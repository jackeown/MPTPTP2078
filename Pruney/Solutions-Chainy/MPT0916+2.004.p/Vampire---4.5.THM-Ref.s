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
% DateTime   : Thu Dec  3 12:59:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 322 expanded)
%              Number of leaves         :   20 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  272 (1076 expanded)
%              Number of equality atoms :   62 ( 123 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f321,f338,f418,f621,f729,f901,f986,f1125])).

fof(f1125,plain,
    ( spl9_4
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | spl9_4
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(unit_resulting_resolution,[],[f72,f1039,f199,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f199,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(unit_resulting_resolution,[],[f94,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f94,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f66,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f36,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f1039,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl9_4
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(forward_demodulation,[],[f154,f1009])).

fof(f1009,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(unit_resulting_resolution,[],[f319,f311,f315,f67,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f67,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f35,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f315,plain,
    ( k1_xboole_0 != sK2
    | spl9_8 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl9_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f311,plain,
    ( k1_xboole_0 != sK0
    | spl9_7 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl9_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f319,plain,
    ( k1_xboole_0 != sK1
    | spl9_9 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl9_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f154,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl9_4
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f986,plain,
    ( spl9_5
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | spl9_5
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f72,f198,f942,f43])).

fof(f942,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl9_5
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f158,f620])).

fof(f620,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl9_12
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f158,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl9_5
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f198,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(unit_resulting_resolution,[],[f94,f53])).

fof(f901,plain,(
    ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f897])).

fof(f897,plain,
    ( $false
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f64,f60,f738,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f738,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_9 ),
    inference(backward_demodulation,[],[f288,f320])).

fof(f320,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f318])).

fof(f288,plain,(
    ~ r1_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f75,f273,f61])).

fof(f273,plain,(
    ~ r1_xboole_0(sK4,sK1) ),
    inference(unit_resulting_resolution,[],[f75,f266,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f266,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(unit_resulting_resolution,[],[f199,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f75,plain,(
    r1_tarski(sK4,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f729,plain,(
    ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f64,f60,f633,f61])).

fof(f633,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f123,f316])).

fof(f316,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f314])).

fof(f123,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f73,f111,f61])).

fof(f111,plain,(
    ~ r1_xboole_0(sK5,sK2) ),
    inference(unit_resulting_resolution,[],[f73,f104,f62])).

fof(f104,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(unit_resulting_resolution,[],[f95,f47])).

fof(f95,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(unit_resulting_resolution,[],[f66,f54])).

fof(f73,plain,(
    r1_tarski(sK5,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f50])).

fof(f37,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f621,plain,
    ( spl9_12
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(avatar_split_clause,[],[f125,f318,f314,f310,f618])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f418,plain,(
    ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f64,f60,f349,f61])).

fof(f349,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f235,f312])).

fof(f312,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f310])).

fof(f235,plain,(
    ~ r1_xboole_0(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f81,f220,f61])).

fof(f220,plain,(
    ~ r1_xboole_0(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f81,f213,f62])).

fof(f213,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f198,f47])).

fof(f81,plain,(
    r1_tarski(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f39,f50])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f338,plain,
    ( spl9_3
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl9_3
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f72,f95,f323,f43])).

fof(f323,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl9_3
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f150,f308])).

fof(f308,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl9_6
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f150,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_3
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f321,plain,
    ( spl9_6
    | spl9_7
    | spl9_8
    | spl9_9 ),
    inference(avatar_split_clause,[],[f127,f318,f314,f310,f306])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    inference(resolution,[],[f67,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f159,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f34,f156,f152,f148])).

fof(f34,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:57:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (18708)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (18732)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (18713)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (18720)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (18719)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18716)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (18730)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (18722)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (18711)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (18709)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (18712)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (18721)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (18710)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (18707)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (18714)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (18709)Refutation not found, incomplete strategy% (18709)------------------------------
% 0.22/0.54  % (18709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18709)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18709)Memory used [KB]: 10874
% 0.22/0.54  % (18709)Time elapsed: 0.127 s
% 0.22/0.54  % (18709)------------------------------
% 0.22/0.54  % (18709)------------------------------
% 0.22/0.54  % (18724)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (18717)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (18723)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (18736)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (18726)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18727)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18725)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18715)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (18729)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (18734)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (18728)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (18733)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (18735)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (18715)Refutation not found, incomplete strategy% (18715)------------------------------
% 0.22/0.55  % (18715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18715)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18715)Memory used [KB]: 10746
% 0.22/0.55  % (18715)Time elapsed: 0.150 s
% 0.22/0.55  % (18715)------------------------------
% 0.22/0.55  % (18715)------------------------------
% 0.22/0.55  % (18731)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (18718)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (18717)Refutation not found, incomplete strategy% (18717)------------------------------
% 0.22/0.56  % (18717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18717)Memory used [KB]: 10746
% 0.22/0.56  % (18717)Time elapsed: 0.141 s
% 0.22/0.56  % (18717)------------------------------
% 0.22/0.56  % (18717)------------------------------
% 0.22/0.57  % (18711)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f1126,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f159,f321,f338,f418,f621,f729,f901,f986,f1125])).
% 0.22/0.57  fof(f1125,plain,(
% 0.22/0.57    spl9_4 | spl9_7 | spl9_8 | spl9_9),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f1120])).
% 0.22/0.57  fof(f1120,plain,(
% 0.22/0.57    $false | (spl9_4 | spl9_7 | spl9_8 | spl9_9)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f1039,f199,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f94,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f66,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.22/0.57    inference(definition_unfolding,[],[f36,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f20])).
% 0.22/0.57  fof(f20,conjecture,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.22/0.57  fof(f1039,plain,(
% 0.22/0.57    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | (spl9_4 | spl9_7 | spl9_8 | spl9_9)),
% 0.22/0.57    inference(forward_demodulation,[],[f154,f1009])).
% 0.22/0.57  fof(f1009,plain,(
% 0.22/0.57    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | (spl9_7 | spl9_8 | spl9_9)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f319,f311,f315,f67,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f41,f48])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.57    inference(definition_unfolding,[],[f35,f48])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f315,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | spl9_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f314])).
% 0.22/0.57  fof(f314,plain,(
% 0.22/0.57    spl9_8 <=> k1_xboole_0 = sK2),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.57  fof(f311,plain,(
% 0.22/0.57    k1_xboole_0 != sK0 | spl9_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f310])).
% 0.22/0.57  fof(f310,plain,(
% 0.22/0.57    spl9_7 <=> k1_xboole_0 = sK0),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.57  fof(f319,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | spl9_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f318])).
% 0.22/0.57  fof(f318,plain,(
% 0.22/0.57    spl9_9 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.57  fof(f154,plain,(
% 0.22/0.57    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl9_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f152])).
% 0.22/0.57  fof(f152,plain,(
% 0.22/0.57    spl9_4 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f986,plain,(
% 0.22/0.57    spl9_5 | ~spl9_12),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f980])).
% 0.22/0.57  fof(f980,plain,(
% 0.22/0.57    $false | (spl9_5 | ~spl9_12)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f198,f942,f43])).
% 0.22/0.57  fof(f942,plain,(
% 0.22/0.57    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | (spl9_5 | ~spl9_12)),
% 0.22/0.57    inference(backward_demodulation,[],[f158,f620])).
% 0.22/0.57  fof(f620,plain,(
% 0.22/0.57    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl9_12),
% 0.22/0.57    inference(avatar_component_clause,[],[f618])).
% 0.22/0.57  fof(f618,plain,(
% 0.22/0.57    spl9_12 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.57  fof(f158,plain,(
% 0.22/0.57    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl9_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f156])).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    spl9_5 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.57  fof(f198,plain,(
% 0.22/0.57    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f94,f53])).
% 0.22/0.57  fof(f901,plain,(
% 0.22/0.57    ~spl9_9),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f897])).
% 0.22/0.57  fof(f897,plain,(
% 0.22/0.57    $false | ~spl9_9),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f64,f60,f738,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.57  fof(f738,plain,(
% 0.22/0.57    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl9_9),
% 0.22/0.57    inference(backward_demodulation,[],[f288,f320])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | ~spl9_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f318])).
% 0.22/0.57  fof(f288,plain,(
% 0.22/0.57    ~r1_xboole_0(sK1,sK1)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f75,f273,f61])).
% 0.22/0.57  fof(f273,plain,(
% 0.22/0.57    ~r1_xboole_0(sK4,sK1)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f75,f266,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.57    inference(flattening,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.57  fof(f266,plain,(
% 0.22/0.57    ~v1_xboole_0(sK4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f199,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    r1_tarski(sK4,sK1)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f38,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.57  fof(f729,plain,(
% 0.22/0.57    ~spl9_8),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f725])).
% 0.22/0.57  fof(f725,plain,(
% 0.22/0.57    $false | ~spl9_8),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f64,f60,f633,f61])).
% 0.22/0.57  fof(f633,plain,(
% 0.22/0.57    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl9_8),
% 0.22/0.57    inference(backward_demodulation,[],[f123,f316])).
% 0.22/0.57  fof(f316,plain,(
% 0.22/0.57    k1_xboole_0 = sK2 | ~spl9_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f314])).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    ~r1_xboole_0(sK2,sK2)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f73,f111,f61])).
% 0.22/0.57  fof(f111,plain,(
% 0.22/0.57    ~r1_xboole_0(sK5,sK2)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f73,f104,f62])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    ~v1_xboole_0(sK5)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f95,f47])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f66,f54])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    r1_tarski(sK5,sK2)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f50])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f621,plain,(
% 0.22/0.57    spl9_12 | spl9_7 | spl9_8 | spl9_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f125,f318,f314,f310,f618])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.22/0.57    inference(resolution,[],[f67,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f40,f48])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f418,plain,(
% 0.22/0.57    ~spl9_7),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f414])).
% 0.22/0.57  fof(f414,plain,(
% 0.22/0.57    $false | ~spl9_7),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f64,f60,f349,f61])).
% 0.22/0.57  fof(f349,plain,(
% 0.22/0.57    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl9_7),
% 0.22/0.57    inference(backward_demodulation,[],[f235,f312])).
% 0.22/0.57  fof(f312,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | ~spl9_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f310])).
% 0.22/0.57  fof(f235,plain,(
% 0.22/0.57    ~r1_xboole_0(sK0,sK0)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f81,f220,f61])).
% 0.22/0.57  fof(f220,plain,(
% 0.22/0.57    ~r1_xboole_0(sK3,sK0)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f81,f213,f62])).
% 0.22/0.57  fof(f213,plain,(
% 0.22/0.57    ~v1_xboole_0(sK3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f198,f47])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    r1_tarski(sK3,sK0)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f39,f50])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f338,plain,(
% 0.22/0.57    spl9_3 | ~spl9_6),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f331])).
% 0.22/0.57  fof(f331,plain,(
% 0.22/0.57    $false | (spl9_3 | ~spl9_6)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f72,f95,f323,f43])).
% 0.22/0.57  fof(f323,plain,(
% 0.22/0.57    ~r2_hidden(k2_mcart_1(sK6),sK5) | (spl9_3 | ~spl9_6)),
% 0.22/0.57    inference(backward_demodulation,[],[f150,f308])).
% 0.22/0.57  fof(f308,plain,(
% 0.22/0.57    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl9_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f306])).
% 0.22/0.57  fof(f306,plain,(
% 0.22/0.57    spl9_6 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.57  fof(f150,plain,(
% 0.22/0.57    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl9_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f148])).
% 0.22/0.57  fof(f148,plain,(
% 0.22/0.57    spl9_3 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.57  fof(f321,plain,(
% 0.22/0.57    spl9_6 | spl9_7 | spl9_8 | spl9_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f127,f318,f314,f310,f306])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.22/0.57    inference(resolution,[],[f67,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f42,f48])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f159,plain,(
% 0.22/0.57    ~spl9_3 | ~spl9_4 | ~spl9_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f34,f156,f152,f148])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (18711)------------------------------
% 0.22/0.57  % (18711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18711)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (18711)Memory used [KB]: 6524
% 0.22/0.57  % (18711)Time elapsed: 0.161 s
% 0.22/0.57  % (18711)------------------------------
% 0.22/0.57  % (18711)------------------------------
% 0.22/0.57  % (18729)Refutation not found, incomplete strategy% (18729)------------------------------
% 0.22/0.57  % (18729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18706)Success in time 0.208 s
%------------------------------------------------------------------------------
