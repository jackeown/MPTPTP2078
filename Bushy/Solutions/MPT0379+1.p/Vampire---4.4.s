%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t61_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 7.27s
% Output     : Refutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 326 expanded)
%              Number of leaves         :   16 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  272 (1227 expanded)
%              Number of equality atoms :   63 ( 181 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f342,f1351,f32374,f32496,f32619,f32743,f32868,f32994,f33121,f33249])).

fof(f33249,plain,
    ( spl12_7
    | ~ spl12_8 ),
    inference(avatar_contradiction_clause,[],[f33245])).

fof(f33245,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f85,f34,f33123,f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d2_subset_1)).

fof(f33123,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl12_7
    | ~ spl12_8 ),
    inference(backward_demodulation,[],[f32337,f1384])).

fof(f1384,plain,
    ( ~ r2_hidden(sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0)
    | ~ spl12_7 ),
    inference(unit_resulting_resolution,[],[f363,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d3_tarski)).

fof(f363,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_7 ),
    inference(unit_resulting_resolution,[],[f341,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d1_zfmisc_1)).

fof(f341,plain,
    ( ~ r2_hidden(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl12_7
  <=> ~ r2_hidden(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f32337,plain,
    ( sK1 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f32336])).

fof(f32336,plain,
    ( spl12_8
  <=> sK1 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f34,plain,(
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
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
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
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
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
                               => ( k1_xboole_0 != X0
                                 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
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
                             => ( k1_xboole_0 != X0
                               => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',t61_subset_1)).

fof(f85,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f27,f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',t6_boole)).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f33121,plain,
    ( spl12_7
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f33117])).

fof(f33117,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_20 ),
    inference(unit_resulting_resolution,[],[f85,f33,f32996,f60])).

fof(f32996,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl12_7
    | ~ spl12_20 ),
    inference(backward_demodulation,[],[f32373,f1384])).

fof(f32373,plain,
    ( sK2 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f32372])).

fof(f32372,plain,
    ( spl12_20
  <=> sK2 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f33,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32994,plain,
    ( spl12_7
    | ~ spl12_18 ),
    inference(avatar_contradiction_clause,[],[f32990])).

fof(f32990,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_18 ),
    inference(unit_resulting_resolution,[],[f85,f32,f32870,f60])).

fof(f32870,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl12_7
    | ~ spl12_18 ),
    inference(backward_demodulation,[],[f32367,f1384])).

fof(f32367,plain,
    ( sK3 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f32366])).

fof(f32366,plain,
    ( spl12_18
  <=> sK3 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f32,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32868,plain,
    ( spl12_7
    | ~ spl12_16 ),
    inference(avatar_contradiction_clause,[],[f32864])).

fof(f32864,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_16 ),
    inference(unit_resulting_resolution,[],[f85,f31,f32745,f60])).

fof(f32745,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl12_7
    | ~ spl12_16 ),
    inference(backward_demodulation,[],[f32361,f1384])).

fof(f32361,plain,
    ( sK4 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f32360])).

fof(f32360,plain,
    ( spl12_16
  <=> sK4 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f31,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32743,plain,
    ( spl12_7
    | ~ spl12_14 ),
    inference(avatar_contradiction_clause,[],[f32739])).

fof(f32739,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f85,f30,f32621,f60])).

fof(f32621,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl12_7
    | ~ spl12_14 ),
    inference(backward_demodulation,[],[f32355,f1384])).

fof(f32355,plain,
    ( sK5 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f32354])).

fof(f32354,plain,
    ( spl12_14
  <=> sK5 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f30,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32619,plain,
    ( spl12_7
    | ~ spl12_12 ),
    inference(avatar_contradiction_clause,[],[f32615])).

fof(f32615,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f85,f29,f32498,f60])).

fof(f32498,plain,
    ( ~ r2_hidden(sK6,sK0)
    | ~ spl12_7
    | ~ spl12_12 ),
    inference(backward_demodulation,[],[f32349,f1384])).

fof(f32349,plain,
    ( sK6 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f32348])).

fof(f32348,plain,
    ( spl12_12
  <=> sK6 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f29,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32496,plain,
    ( spl12_7
    | ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f32492])).

fof(f32492,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_10 ),
    inference(unit_resulting_resolution,[],[f85,f26,f32376,f60])).

fof(f32376,plain,
    ( ~ r2_hidden(sK7,sK0)
    | ~ spl12_7
    | ~ spl12_10 ),
    inference(backward_demodulation,[],[f32343,f1384])).

fof(f32343,plain,
    ( sK7 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f32342])).

fof(f32342,plain,
    ( spl12_10
  <=> sK7 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f26,plain,(
    m1_subset_1(sK7,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32374,plain,
    ( spl12_8
    | spl12_10
    | spl12_12
    | spl12_14
    | spl12_16
    | spl12_18
    | spl12_20
    | spl12_7 ),
    inference(avatar_split_clause,[],[f2106,f340,f32372,f32366,f32360,f32354,f32348,f32342,f32336])).

fof(f2106,plain,
    ( sK2 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK3 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK4 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK5 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK6 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK7 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK1 = sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ spl12_7 ),
    inference(resolution,[],[f1383,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ r2_hidden(X8,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))
      | X1 = X8
      | X2 = X8
      | X3 = X8
      | X4 = X8
      | X5 = X8
      | X6 = X8
      | X0 = X8 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X8
      | X1 = X8
      | X2 = X8
      | X3 = X8
      | X4 = X8
      | X5 = X8
      | X6 = X8
      | ~ r2_hidden(X8,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d5_enumset1)).

fof(f1383,plain,
    ( r2_hidden(sK11(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl12_7 ),
    inference(unit_resulting_resolution,[],[f363,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1351,plain,(
    ~ spl12_4 ),
    inference(avatar_contradiction_clause,[],[f1346])).

fof(f1346,plain,
    ( $false
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f1115,f1118,f1336,f60])).

fof(f1336,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_4 ),
    inference(superposition,[],[f1277,f1101])).

fof(f1101,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f335,f56])).

fof(f335,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl12_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f1277,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f1260,f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',t7_boole)).

fof(f1260,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f1188,f68])).

fof(f1188,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f1118,f63])).

fof(f1118,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl12_4 ),
    inference(backward_demodulation,[],[f1101,f1107])).

fof(f1107,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(sK0))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f335,f65])).

fof(f1115,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl12_4 ),
    inference(backward_demodulation,[],[f1101,f1104])).

fof(f1104,plain,
    ( m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f335,f335,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f342,plain,
    ( spl12_4
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f218,f340,f334])).

fof(f218,plain,
    ( ~ r2_hidden(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f28,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
