%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t59_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 7.00s
% Output     : Refutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 260 expanded)
%              Number of leaves         :   14 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 ( 859 expanded)
%              Number of equality atoms :   49 ( 137 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f240,f3727,f17516,f17648,f17781,f17915,f18050,f18186])).

fof(f18186,plain,
    ( spl10_7
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f18182])).

fof(f18182,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f75,f32,f18052,f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d2_subset_1)).

fof(f18052,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f17491,f3841])).

fof(f3841,plain,
    ( ~ r2_hidden(sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),sK0)
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f261,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d3_tarski)).

fof(f261,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f239,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d1_zfmisc_1)).

fof(f239,plain,
    ( ~ r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl10_7
  <=> ~ r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f17491,plain,
    ( sK1 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f17490])).

fof(f17490,plain,
    ( spl10_8
  <=> sK1 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f32,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
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
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
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
                       => ( k1_xboole_0 != X0
                         => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
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
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',t59_subset_1)).

fof(f75,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f27,f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',t6_boole)).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18050,plain,
    ( spl10_7
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f18046])).

fof(f18046,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_16 ),
    inference(unit_resulting_resolution,[],[f75,f31,f17917,f54])).

fof(f17917,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl10_7
    | ~ spl10_16 ),
    inference(backward_demodulation,[],[f17515,f3841])).

fof(f17515,plain,
    ( sK2 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f17514])).

fof(f17514,plain,
    ( spl10_16
  <=> sK2 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f31,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f17915,plain,
    ( spl10_7
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f17911])).

fof(f17911,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f75,f30,f17783,f54])).

fof(f17783,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl10_7
    | ~ spl10_14 ),
    inference(backward_demodulation,[],[f17509,f3841])).

fof(f17509,plain,
    ( sK3 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f17508])).

fof(f17508,plain,
    ( spl10_14
  <=> sK3 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f30,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f17781,plain,
    ( spl10_7
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f17777])).

fof(f17777,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f75,f29,f17650,f54])).

fof(f17650,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl10_7
    | ~ spl10_12 ),
    inference(backward_demodulation,[],[f17503,f3841])).

fof(f17503,plain,
    ( sK4 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f17502])).

fof(f17502,plain,
    ( spl10_12
  <=> sK4 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f29,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f17648,plain,
    ( spl10_7
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f17644])).

fof(f17644,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f75,f26,f17518,f54])).

fof(f17518,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f17497,f3841])).

fof(f17497,plain,
    ( sK5 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f17496])).

fof(f17496,plain,
    ( spl10_10
  <=> sK5 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f26,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f17516,plain,
    ( spl10_8
    | spl10_10
    | spl10_12
    | spl10_14
    | spl10_16
    | spl10_7 ),
    inference(avatar_split_clause,[],[f3964,f238,f17514,f17508,f17502,f17496,f17490])).

fof(f3964,plain,
    ( sK2 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK3 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK4 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK5 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | sK1 = sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0)
    | ~ spl10_7 ),
    inference(resolution,[],[f3840,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k3_enumset1(X0,X1,X2,X3,X4))
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | X4 = X6
      | X0 = X6 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | X4 = X6
      | ~ r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d3_enumset1)).

fof(f3840,plain,
    ( r2_hidden(sK9(k3_enumset1(sK1,sK2,sK3,sK4,sK5),sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f261,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3727,plain,(
    ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f3722])).

fof(f3722,plain,
    ( $false
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f3337,f3350,f3667,f54])).

fof(f3667,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_4 ),
    inference(superposition,[],[f3577,f3313])).

fof(f3313,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f233,f50])).

fof(f233,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl10_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f3577,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f3562,f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',t7_boole)).

fof(f3562,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f3467,f62])).

fof(f3467,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f3350,f57])).

fof(f3350,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f3313,f3329])).

fof(f3329,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(sK0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f233,f59])).

fof(f3337,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f3313,f3316])).

fof(f3316,plain,
    ( m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f233,f233,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f240,plain,
    ( spl10_4
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f136,f238,f232])).

fof(f136,plain,
    ( ~ r2_hidden(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f28,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
