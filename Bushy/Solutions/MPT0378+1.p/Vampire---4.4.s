%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t60_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 7.17s
% Output     : Refutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 293 expanded)
%              Number of leaves         :   15 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  249 (1035 expanded)
%              Number of equality atoms :   56 ( 159 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f300,f1378,f29128,f29295,f29463,f29632,f29802,f29973,f30145])).

fof(f30145,plain,
    ( spl11_7
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f30141])).

fof(f30141,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f80,f33,f29975,f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',d2_subset_1)).

fof(f29975,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(backward_demodulation,[],[f29097,f1401])).

fof(f1401,plain,
    ( ~ r2_hidden(sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),sK0)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f321,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',d3_tarski)).

fof(f321,plain,
    ( ~ r1_tarski(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f299,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',d1_zfmisc_1)).

fof(f299,plain,
    ( ~ r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl11_7
  <=> ~ r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f29097,plain,
    ( sK1 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f29096])).

fof(f29096,plain,
    ( spl11_8
  <=> sK1 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f33,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
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
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
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
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
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
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',t60_subset_1)).

fof(f80,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f27,f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',t6_boole)).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f29973,plain,
    ( spl11_7
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f29969])).

fof(f29969,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f80,f32,f29804,f57])).

fof(f29804,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(backward_demodulation,[],[f29127,f1401])).

fof(f29127,plain,
    ( sK2 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f29126])).

fof(f29126,plain,
    ( spl11_18
  <=> sK2 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f32,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f29802,plain,
    ( spl11_7
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f29798])).

fof(f29798,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f80,f31,f29634,f57])).

fof(f29634,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl11_7
    | ~ spl11_16 ),
    inference(backward_demodulation,[],[f29121,f1401])).

fof(f29121,plain,
    ( sK3 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f29120])).

fof(f29120,plain,
    ( spl11_16
  <=> sK3 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f31,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f29632,plain,
    ( spl11_7
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f29628])).

fof(f29628,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_14 ),
    inference(unit_resulting_resolution,[],[f80,f30,f29465,f57])).

fof(f29465,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl11_7
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f29115,f1401])).

fof(f29115,plain,
    ( sK4 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f29114])).

fof(f29114,plain,
    ( spl11_14
  <=> sK4 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f30,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f29463,plain,
    ( spl11_7
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f29459])).

fof(f29459,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f80,f29,f29297,f57])).

fof(f29297,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl11_7
    | ~ spl11_12 ),
    inference(backward_demodulation,[],[f29109,f1401])).

fof(f29109,plain,
    ( sK5 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f29108])).

fof(f29108,plain,
    ( spl11_12
  <=> sK5 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f29,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f29295,plain,
    ( spl11_7
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f29291])).

fof(f29291,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f80,f26,f29130,f57])).

fof(f29130,plain,
    ( ~ r2_hidden(sK6,sK0)
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(backward_demodulation,[],[f29103,f1401])).

fof(f29103,plain,
    ( sK6 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f29102])).

fof(f29102,plain,
    ( spl11_10
  <=> sK6 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f26,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f29128,plain,
    ( spl11_8
    | spl11_10
    | spl11_12
    | spl11_14
    | spl11_16
    | spl11_18
    | spl11_7 ),
    inference(avatar_split_clause,[],[f1615,f298,f29126,f29120,f29114,f29108,f29102,f29096])).

fof(f1615,plain,
    ( sK2 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK3 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK4 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK5 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK6 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | sK1 = sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl11_7 ),
    inference(resolution,[],[f1400,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(X7,k4_enumset1(X0,X1,X2,X3,X4,X5))
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | X5 = X7
      | X0 = X7 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X7
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | X5 = X7
      | ~ r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',d4_enumset1)).

fof(f1400,plain,
    ( r2_hidden(sK10(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f321,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1378,plain,(
    ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f1373])).

fof(f1373,plain,
    ( $false
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f1114,f1117,f1363,f57])).

fof(f1363,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl11_4 ),
    inference(superposition,[],[f1306,f1100])).

fof(f1100,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f293,f53])).

fof(f293,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl11_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1306,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f1286,f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t60_subset_1.p',t7_boole)).

fof(f1286,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f1185,f65])).

fof(f1185,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f1117,f60])).

fof(f1117,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_4 ),
    inference(backward_demodulation,[],[f1100,f1106])).

fof(f1106,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(sK0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f293,f62])).

fof(f1114,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl11_4 ),
    inference(backward_demodulation,[],[f1100,f1103])).

fof(f1103,plain,
    ( m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f293,f293,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f300,plain,
    ( spl11_4
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f190,f298,f292])).

fof(f190,plain,
    ( ~ r2_hidden(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f28,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
