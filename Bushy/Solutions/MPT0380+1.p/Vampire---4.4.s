%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t62_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 7.56s
% Output     : Refutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 359 expanded)
%              Number of leaves         :   17 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  295 (1435 expanded)
%              Number of equality atoms :   70 ( 203 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f414,f5917,f45210,f45283,f45357,f45432,f45508,f45585,f45663,f45742,f45822])).

fof(f45822,plain,
    ( spl13_7
    | ~ spl13_8 ),
    inference(avatar_contradiction_clause,[],[f45818])).

fof(f45818,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f90,f35,f45744,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',d2_subset_1)).

fof(f45744,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl13_7
    | ~ spl13_8 ),
    inference(backward_demodulation,[],[f45167,f6011])).

fof(f6011,plain,
    ( ~ r2_hidden(sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),sK0)
    | ~ spl13_7 ),
    inference(unit_resulting_resolution,[],[f435,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK12(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',d3_tarski)).

fof(f435,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_7 ),
    inference(unit_resulting_resolution,[],[f413,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',d1_zfmisc_1)).

fof(f413,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl13_7
  <=> ~ r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f45167,plain,
    ( sK1 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f45166])).

fof(f45166,plain,
    ( spl13_8
  <=> sK1 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f35,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ! [X8] :
                                    ( m1_subset_1(X8,X0)
                                   => ( k1_xboole_0 != X0
                                     => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ! [X8] :
                                  ( m1_subset_1(X8,X0)
                                 => ( k1_xboole_0 != X0
                                   => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',t62_subset_1)).

fof(f90,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f27,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',t6_boole)).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f45742,plain,
    ( spl13_7
    | ~ spl13_22 ),
    inference(avatar_contradiction_clause,[],[f45738])).

fof(f45738,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f90,f34,f45665,f63])).

fof(f45665,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl13_7
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f45209,f6011])).

fof(f45209,plain,
    ( sK2 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f45208])).

fof(f45208,plain,
    ( spl13_22
  <=> sK2 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f34,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45663,plain,
    ( spl13_7
    | ~ spl13_20 ),
    inference(avatar_contradiction_clause,[],[f45659])).

fof(f45659,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f90,f33,f45587,f63])).

fof(f45587,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl13_7
    | ~ spl13_20 ),
    inference(backward_demodulation,[],[f45203,f6011])).

fof(f45203,plain,
    ( sK3 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f45202])).

fof(f45202,plain,
    ( spl13_20
  <=> sK3 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f33,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45585,plain,
    ( spl13_7
    | ~ spl13_18 ),
    inference(avatar_contradiction_clause,[],[f45581])).

fof(f45581,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f90,f32,f45510,f63])).

fof(f45510,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl13_7
    | ~ spl13_18 ),
    inference(backward_demodulation,[],[f45197,f6011])).

fof(f45197,plain,
    ( sK4 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f45196])).

fof(f45196,plain,
    ( spl13_18
  <=> sK4 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f32,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45508,plain,
    ( spl13_7
    | ~ spl13_16 ),
    inference(avatar_contradiction_clause,[],[f45504])).

fof(f45504,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f90,f31,f45434,f63])).

fof(f45434,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl13_7
    | ~ spl13_16 ),
    inference(backward_demodulation,[],[f45191,f6011])).

fof(f45191,plain,
    ( sK5 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f45190])).

fof(f45190,plain,
    ( spl13_16
  <=> sK5 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f31,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45432,plain,
    ( spl13_7
    | ~ spl13_14 ),
    inference(avatar_contradiction_clause,[],[f45428])).

fof(f45428,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f90,f30,f45359,f63])).

fof(f45359,plain,
    ( ~ r2_hidden(sK6,sK0)
    | ~ spl13_7
    | ~ spl13_14 ),
    inference(backward_demodulation,[],[f45185,f6011])).

fof(f45185,plain,
    ( sK6 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f45184])).

fof(f45184,plain,
    ( spl13_14
  <=> sK6 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f30,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45357,plain,
    ( spl13_7
    | ~ spl13_12 ),
    inference(avatar_contradiction_clause,[],[f45353])).

fof(f45353,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f90,f29,f45285,f63])).

fof(f45285,plain,
    ( ~ r2_hidden(sK7,sK0)
    | ~ spl13_7
    | ~ spl13_12 ),
    inference(backward_demodulation,[],[f45179,f6011])).

fof(f45179,plain,
    ( sK7 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f45178])).

fof(f45178,plain,
    ( spl13_12
  <=> sK7 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f29,plain,(
    m1_subset_1(sK7,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45283,plain,
    ( spl13_7
    | ~ spl13_10 ),
    inference(avatar_contradiction_clause,[],[f45279])).

fof(f45279,plain,
    ( $false
    | ~ spl13_7
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f90,f26,f45212,f63])).

fof(f45212,plain,
    ( ~ r2_hidden(sK8,sK0)
    | ~ spl13_7
    | ~ spl13_10 ),
    inference(backward_demodulation,[],[f45173,f6011])).

fof(f45173,plain,
    ( sK8 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f45172])).

fof(f45172,plain,
    ( spl13_10
  <=> sK8 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f26,plain,(
    m1_subset_1(sK8,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45210,plain,
    ( spl13_8
    | spl13_10
    | spl13_12
    | spl13_14
    | spl13_16
    | spl13_18
    | spl13_20
    | spl13_22
    | spl13_7 ),
    inference(avatar_split_clause,[],[f7871,f412,f45208,f45202,f45196,f45190,f45184,f45178,f45172,f45166])).

fof(f7871,plain,
    ( sK2 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK3 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK4 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK5 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK6 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK7 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK8 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | sK1 = sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl13_7 ),
    inference(resolution,[],[f6010,f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
      | X1 = X9
      | X2 = X9
      | X3 = X9
      | X4 = X9
      | X5 = X9
      | X6 = X9
      | X7 = X9
      | X0 = X9 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X0 = X9
      | X1 = X9
      | X2 = X9
      | X3 = X9
      | X4 = X9
      | X5 = X9
      | X6 = X9
      | X7 = X9
      | ~ r2_hidden(X9,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',d6_enumset1)).

fof(f6010,plain,
    ( r2_hidden(sK12(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl13_7 ),
    inference(unit_resulting_resolution,[],[f435,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK12(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5917,plain,(
    ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f5912])).

fof(f5912,plain,
    ( $false
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f5644,f5647,f5902,f63])).

fof(f5902,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl13_4 ),
    inference(superposition,[],[f5892,f5631])).

fof(f5631,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f407,f59])).

fof(f407,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl13_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f5892,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f5862,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t62_subset_1.p',t7_boole)).

fof(f5862,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f5774,f71])).

fof(f5774,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f5647,f66])).

fof(f5647,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl13_4 ),
    inference(backward_demodulation,[],[f5631,f5636])).

fof(f5636,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(sK0))
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f407,f68])).

fof(f5644,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl13_4 ),
    inference(backward_demodulation,[],[f5631,f5633])).

fof(f5633,plain,
    ( m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f407,f407,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f414,plain,
    ( spl13_4
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f250,f412,f406])).

fof(f250,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f28,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
