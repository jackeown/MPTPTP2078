%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t51_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:24 EDT 2019

% Result     : Theorem 1.14s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  635 (2781 expanded)
%              Number of leaves         :  120 ( 953 expanded)
%              Depth                    :   14
%              Number of atoms          : 1825 (7869 expanded)
%              Number of equality atoms :  149 ( 932 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f95,f102,f117,f164,f184,f211,f295,f302,f309,f319,f326,f402,f468,f501,f603,f797,f824,f885,f1317,f1466,f1645,f1652,f1659,f1820,f2208,f2220,f2309,f2316,f2401,f2668,f2783,f2851,f2858,f2968,f3427,f3434,f3441,f3586,f3639,f3759,f3844,f4014,f4039,f4595,f4652,f4659,f4669,f4679,f4686,f4718,f4719,f4721,f4723,f4748,f4805,f4897,f4921,f5126,f5201,f5279,f5809,f5811,f6027,f6288,f6294,f6297,f6326,f6866,f6923,f7003,f7011,f7037,f7043,f7053,f7067,f7071,f7078,f7234,f7272,f7298,f7329,f7501,f7598,f7669,f7865,f8041,f8225,f8328,f8366,f8498,f8546,f8550,f9258,f9338,f9350,f9353,f9357,f9358,f9413,f9511,f10458,f10506,f10523,f10533,f10636,f10746,f11792,f11948,f12214,f12231,f12309,f12320,f12886,f13100,f13126])).

fof(f13126,plain,
    ( spl7_5
    | ~ spl7_22
    | ~ spl7_70
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(avatar_contradiction_clause,[],[f13125])).

fof(f13125,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_70
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(subsumption_resolution,[],[f13124,f101])).

fof(f101,plain,
    ( k3_subset_1(sK0,sK2) != sK1
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_5
  <=> k3_subset_1(sK0,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f13124,plain,
    ( k3_subset_1(sK0,sK2) = sK1
    | ~ spl7_22
    | ~ spl7_70
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(backward_demodulation,[],[f12934,f294])).

fof(f294,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl7_22
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f12934,plain,
    ( k4_xboole_0(sK0,sK2) = sK1
    | ~ spl7_70
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(backward_demodulation,[],[f12915,f2857])).

fof(f2857,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f2856])).

fof(f2856,plain,
    ( spl7_70
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f12915,plain,
    ( k3_subset_1(sK0,sK1) = sK2
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(subsumption_resolution,[],[f12914,f8545])).

fof(f8545,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl7_152 ),
    inference(avatar_component_clause,[],[f8544])).

fof(f8544,plain,
    ( spl7_152
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f12914,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,sK1) = sK2
    | ~ spl7_178 ),
    inference(resolution,[],[f12885,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',d10_xboole_0)).

fof(f12885,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl7_178 ),
    inference(avatar_component_clause,[],[f12884])).

fof(f12884,plain,
    ( spl7_178
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f13100,plain,
    ( spl7_5
    | ~ spl7_32
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(avatar_contradiction_clause,[],[f13099])).

fof(f13099,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_32
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(subsumption_resolution,[],[f12917,f101])).

fof(f12917,plain,
    ( k3_subset_1(sK0,sK2) = sK1
    | ~ spl7_32
    | ~ spl7_152
    | ~ spl7_178 ),
    inference(backward_demodulation,[],[f12915,f325])).

fof(f325,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl7_32
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f12886,plain,
    ( spl7_178
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f12418,f300,f12884])).

fof(f300,plain,
    ( spl7_24
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f12418,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f7315,f7393])).

fof(f7393,plain,
    ( ! [X2] :
        ( r1_tarski(k3_subset_1(sK0,sK1),X2)
        | m1_subset_1(sK5(k3_subset_1(sK0,sK1),X2),sK0) )
    | ~ spl7_24 ),
    inference(resolution,[],[f708,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',t7_boole)).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',d2_subset_1)).

fof(f708,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X7),sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),X7) )
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f697,f301])).

fof(f301,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f300])).

fof(f697,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(k3_subset_1(sK0,sK1),X7),sK0)
        | r1_tarski(k4_xboole_0(sK0,sK1),X7) )
    | ~ spl7_24 ),
    inference(superposition,[],[f166,f301])).

fof(f166,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK5(k4_xboole_0(X3,X4),X5),X3)
      | r1_tarski(k4_xboole_0(X3,X4),X5) ) ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',d3_tarski)).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',d5_xboole_0)).

fof(f7315,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(sK5(k3_subset_1(sK0,sK1),sK2),sK0)
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f7312,f301])).

fof(f7312,plain,
    ( ~ m1_subset_1(sK5(k3_subset_1(sK0,sK1),sK2),sK0)
    | r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl7_24 ),
    inference(superposition,[],[f655,f301])).

fof(f655,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(k4_xboole_0(X0,sK1),sK2),sK0)
      | r1_tarski(k4_xboole_0(X0,sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f641])).

fof(f641,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(X0,sK1),sK2)
      | ~ m1_subset_1(sK5(k4_xboole_0(X0,sK1),sK2),sK0)
      | r1_tarski(k4_xboole_0(X0,sK1),sK2) ) ),
    inference(resolution,[],[f149,f136])).

fof(f136,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK2),sK1)
      | ~ m1_subset_1(sK5(X1,sK2),sK0)
      | r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',t51_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f149,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK5(k4_xboole_0(X3,X4),X5),X4)
      | r1_tarski(k4_xboole_0(X3,X4),X5) ) ),
    inference(resolution,[],[f75,f64])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f12320,plain,
    ( ~ spl7_58
    | spl7_79
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(avatar_contradiction_clause,[],[f12319])).

fof(f12319,plain,
    ( $false
    | ~ spl7_58
    | ~ spl7_79
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(subsumption_resolution,[],[f12318,f3437])).

fof(f3437,plain,
    ( k1_xboole_0 != sK2
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f3436])).

fof(f3436,plain,
    ( spl7_79
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f12318,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_58
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(forward_demodulation,[],[f12317,f12054])).

fof(f12054,plain,
    ( k3_subset_1(sK0,sK1) = k1_xboole_0
    | ~ spl7_58
    | ~ spl7_118 ),
    inference(backward_demodulation,[],[f11953,f11951])).

fof(f11951,plain,
    ( ! [X0] : k3_subset_1(sK0,sK1) = k4_xboole_0(k3_subset_1(sK0,sK1),X0)
    | ~ spl7_118 ),
    inference(resolution,[],[f7049,f582])).

fof(f582,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X10)
      | k4_xboole_0(X10,X11) = X10 ) ),
    inference(resolution,[],[f251,f62])).

fof(f251,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f7049,plain,
    ( v1_xboole_0(k3_subset_1(sK0,sK1))
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f7048])).

fof(f7048,plain,
    ( spl7_118
  <=> v1_xboole_0(k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f11953,plain,
    ( ! [X1] : k4_xboole_0(k3_subset_1(sK0,sK1),X1) = k1_xboole_0
    | ~ spl7_58
    | ~ spl7_118 ),
    inference(resolution,[],[f7049,f2278])).

fof(f2278,plain,
    ( ! [X4,X5] :
        ( ~ v1_xboole_0(X4)
        | k4_xboole_0(X4,X5) = k1_xboole_0 )
    | ~ spl7_58 ),
    inference(resolution,[],[f2232,f246])).

fof(f246,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK3(X6,X7,X8),X8)
      | k4_xboole_0(X6,X7) = X8
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f43,f62])).

fof(f2232,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f2226,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f75,f59])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',t4_boole)).

fof(f2226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK0) )
    | ~ spl7_58 ),
    inference(resolution,[],[f2207,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',l3_subset_1)).

fof(f2207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f2206])).

fof(f2206,plain,
    ( spl7_58
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f12317,plain,
    ( k3_subset_1(sK0,sK1) = sK2
    | ~ spl7_58
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(subsumption_resolution,[],[f12143,f704])).

fof(f704,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f703,f59])).

fof(f703,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(subsumption_resolution,[],[f693,f150])).

fof(f693,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_xboole_0,X1),k1_xboole_0)
      | r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ) ),
    inference(superposition,[],[f166,f59])).

fof(f12143,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k3_subset_1(sK0,sK1) = sK2
    | ~ spl7_58
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f12054,f8607])).

fof(f8607,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | k3_subset_1(sK0,sK1) = sK2
    | ~ spl7_152 ),
    inference(resolution,[],[f8545,f55])).

fof(f12309,plain,
    ( ~ spl7_58
    | spl7_81
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(avatar_contradiction_clause,[],[f12308])).

fof(f12308,plain,
    ( $false
    | ~ spl7_58
    | ~ spl7_81
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(subsumption_resolution,[],[f12139,f3758])).

fof(f3758,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f3757])).

fof(f3757,plain,
    ( spl7_81
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f12139,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_118
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f12054,f8545])).

fof(f12231,plain,
    ( spl7_53
    | ~ spl7_58
    | ~ spl7_70
    | ~ spl7_118 ),
    inference(avatar_contradiction_clause,[],[f12230])).

fof(f12230,plain,
    ( $false
    | ~ spl7_53
    | ~ spl7_58
    | ~ spl7_70
    | ~ spl7_118 ),
    inference(subsumption_resolution,[],[f12229,f1651])).

fof(f1651,plain,
    ( sK0 != sK1
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f1650,plain,
    ( spl7_53
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f12229,plain,
    ( sK0 = sK1
    | ~ spl7_58
    | ~ spl7_70
    | ~ spl7_118 ),
    inference(forward_demodulation,[],[f12071,f60])).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',t3_boole)).

fof(f12071,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK1
    | ~ spl7_58
    | ~ spl7_70
    | ~ spl7_118 ),
    inference(backward_demodulation,[],[f12054,f2857])).

fof(f12214,plain,
    ( ~ spl7_32
    | spl7_53
    | ~ spl7_58
    | ~ spl7_60
    | ~ spl7_118 ),
    inference(avatar_contradiction_clause,[],[f12213])).

fof(f12213,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_53
    | ~ spl7_58
    | ~ spl7_60
    | ~ spl7_118 ),
    inference(subsumption_resolution,[],[f12212,f1651])).

fof(f12212,plain,
    ( sK0 = sK1
    | ~ spl7_32
    | ~ spl7_58
    | ~ spl7_60
    | ~ spl7_118 ),
    inference(forward_demodulation,[],[f12056,f2308])).

fof(f2308,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f2307])).

fof(f2307,plain,
    ( spl7_60
  <=> k3_subset_1(sK0,k1_xboole_0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f12056,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | ~ spl7_32
    | ~ spl7_58
    | ~ spl7_118 ),
    inference(backward_demodulation,[],[f12054,f325])).

fof(f11948,plain,
    ( spl7_176
    | ~ spl7_132 ),
    inference(avatar_split_clause,[],[f7336,f7327,f11946])).

fof(f11946,plain,
    ( spl7_176
  <=> r2_hidden(sK6(k3_subset_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).

fof(f7327,plain,
    ( spl7_132
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | r2_hidden(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f7336,plain,
    ( r2_hidden(sK6(k3_subset_1(sK0,sK1)),sK0)
    | ~ spl7_132 ),
    inference(resolution,[],[f7328,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',existence_m1_subset_1)).

fof(f7328,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | r2_hidden(X7,sK0) )
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f7327])).

fof(f11792,plain,
    ( ~ spl7_175
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f7300,f7296,f11790])).

fof(f11790,plain,
    ( spl7_175
  <=> ~ r2_hidden(sK6(k3_subset_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_175])])).

fof(f7296,plain,
    ( spl7_130
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f7300,plain,
    ( ~ r2_hidden(sK6(k3_subset_1(sK0,sK1)),sK1)
    | ~ spl7_130 ),
    inference(resolution,[],[f7297,f72])).

fof(f7297,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X7,sK1) )
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f7296])).

fof(f10746,plain,
    ( spl7_172
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f10436,f5277,f10744])).

fof(f10744,plain,
    ( spl7_172
  <=> m1_subset_1(sK6(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f5277,plain,
    ( spl7_104
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f10436,plain,
    ( m1_subset_1(sK6(sK1),sK0)
    | ~ spl7_104 ),
    inference(resolution,[],[f6721,f72])).

fof(f6721,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1)
        | m1_subset_1(X1,sK0) )
    | ~ spl7_104 ),
    inference(resolution,[],[f5278,f81])).

fof(f5278,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f5277])).

fof(f10636,plain,
    ( spl7_170
    | ~ spl7_166 ),
    inference(avatar_split_clause,[],[f10529,f10504,f10634])).

fof(f10634,plain,
    ( spl7_170
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f10504,plain,
    ( spl7_166
  <=> k1_xboole_0 = sK6(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f10529,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_166 ),
    inference(superposition,[],[f72,f10505])).

fof(f10505,plain,
    ( k1_xboole_0 = sK6(k1_xboole_0)
    | ~ spl7_166 ),
    inference(avatar_component_clause,[],[f10504])).

fof(f10533,plain,
    ( spl7_20
    | spl7_168 ),
    inference(avatar_split_clause,[],[f405,f10531,f209])).

fof(f209,plain,
    ( spl7_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f10531,plain,
    ( spl7_168
  <=> ! [X3,X4] :
        ( k4_xboole_0(sK2,X3) = X4
        | ~ m1_subset_1(sK3(sK2,X3,X4),sK1)
        | r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ m1_subset_1(sK3(sK2,X3,X4),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f405,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(sK2,X3) = X4
      | ~ m1_subset_1(sK3(sK2,X3,X4),sK0)
      | r2_hidden(sK3(sK2,X3,X4),X4)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK3(sK2,X3,X4),sK1) ) ),
    inference(resolution,[],[f250,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f250,plain,(
    ! [X21,X20] :
      ( ~ r2_hidden(sK3(sK2,X20,X21),sK1)
      | k4_xboole_0(sK2,X20) = X21
      | ~ m1_subset_1(sK3(sK2,X20,X21),sK0)
      | r2_hidden(sK3(sK2,X20,X21),X21) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10523,plain,(
    ~ spl7_154 ),
    inference(avatar_contradiction_clause,[],[f10507])).

fof(f10507,plain,
    ( $false
    | ~ spl7_154 ),
    inference(resolution,[],[f8549,f72])).

fof(f8549,plain,
    ( ! [X1] : ~ m1_subset_1(X1,k1_xboole_0)
    | ~ spl7_154 ),
    inference(avatar_component_clause,[],[f8548])).

fof(f8548,plain,
    ( spl7_154
  <=> ! [X1] : ~ m1_subset_1(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f10506,plain,
    ( spl7_166
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f10454,f1657,f10504])).

fof(f1657,plain,
    ( spl7_54
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f10454,plain,
    ( k1_xboole_0 = sK6(k1_xboole_0)
    | ~ spl7_54 ),
    inference(resolution,[],[f384,f1658])).

fof(f1658,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f384,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | k1_xboole_0 = sK6(X2) ) ),
    inference(resolution,[],[f120,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',t6_boole)).

fof(f120,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f72])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10458,plain,
    ( spl7_20
    | spl7_164 ),
    inference(avatar_split_clause,[],[f392,f10456,f209])).

fof(f10456,plain,
    ( spl7_164
  <=> ! [X3,X4] :
        ( k4_xboole_0(X3,X4) = sK2
        | ~ m1_subset_1(sK3(X3,X4,sK2),sK1)
        | r2_hidden(sK3(X3,X4,sK2),X3)
        | ~ m1_subset_1(sK3(X3,X4,sK2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f392,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X3,X4) = sK2
      | ~ m1_subset_1(sK3(X3,X4,sK2),sK0)
      | r2_hidden(sK3(X3,X4,sK2),X3)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK3(X3,X4,sK2),sK1) ) ),
    inference(resolution,[],[f243,f71])).

fof(f243,plain,(
    ! [X21,X20] :
      ( ~ r2_hidden(sK3(X20,X21,sK2),sK1)
      | k4_xboole_0(X20,X21) = sK2
      | ~ m1_subset_1(sK3(X20,X21,sK2),sK0)
      | r2_hidden(sK3(X20,X21,sK2),X20) ) ),
    inference(resolution,[],[f43,f38])).

fof(f9511,plain,
    ( ~ spl7_161
    | spl7_162 ),
    inference(avatar_split_clause,[],[f3990,f9509,f9503])).

fof(f9503,plain,
    ( spl7_161
  <=> ~ m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_161])])).

fof(f9509,plain,
    ( spl7_162
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f3990,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f3988])).

fof(f3988,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | m1_subset_1(sK1,sK2) ),
    inference(resolution,[],[f337,f107])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,sK0)
      | m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f81,f37])).

fof(f337,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK1,X2)
      | m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(resolution,[],[f107,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',antisymmetry_r2_hidden)).

fof(f9413,plain,
    ( ~ spl7_17
    | ~ spl7_15
    | spl7_5 ),
    inference(avatar_split_clause,[],[f6328,f100,f176,f182])).

fof(f182,plain,
    ( spl7_17
  <=> ~ r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f176,plain,
    ( spl7_15
  <=> ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f6328,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl7_5 ),
    inference(extensionality_resolution,[],[f55,f101])).

fof(f9358,plain,
    ( ~ spl7_35
    | spl7_97 ),
    inference(avatar_split_clause,[],[f6334,f4684,f400])).

fof(f400,plain,
    ( spl7_35
  <=> ~ v1_xboole_0(k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f4684,plain,
    ( spl7_97
  <=> ~ r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f6334,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl7_97 ),
    inference(resolution,[],[f4685,f130])).

fof(f130,plain,(
    ! [X6,X5] :
      ( r1_tarski(X5,X6)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f64,f62])).

fof(f4685,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0)
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f4684])).

fof(f9357,plain,
    ( ~ spl7_97
    | spl7_95 ),
    inference(avatar_split_clause,[],[f9351,f4677,f4684])).

fof(f4677,plain,
    ( spl7_95
  <=> k3_subset_1(sK0,sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f9351,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0)
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f6333,f704])).

fof(f6333,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2))
    | ~ spl7_95 ),
    inference(extensionality_resolution,[],[f55,f4678])).

fof(f4678,plain,
    ( k3_subset_1(sK0,sK2) != k1_xboole_0
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f4677])).

fof(f9353,plain,
    ( spl7_95
    | ~ spl7_96 ),
    inference(avatar_contradiction_clause,[],[f9352])).

fof(f9352,plain,
    ( $false
    | ~ spl7_95
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f4682,f9351])).

fof(f4682,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0)
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f4681])).

fof(f4681,plain,
    ( spl7_96
  <=> r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f9350,plain,
    ( ~ spl7_34
    | spl7_97 ),
    inference(avatar_contradiction_clause,[],[f9349])).

fof(f9349,plain,
    ( $false
    | ~ spl7_34
    | ~ spl7_97 ),
    inference(subsumption_resolution,[],[f398,f6334])).

fof(f398,plain,
    ( v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl7_34
  <=> v1_xboole_0(k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f9338,plain,
    ( spl7_158
    | ~ spl7_22
    | spl7_35 ),
    inference(avatar_split_clause,[],[f3952,f400,f293,f9336])).

fof(f9336,plain,
    ( spl7_158
  <=> r2_hidden(sK6(k3_subset_1(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f3952,plain,
    ( r2_hidden(sK6(k3_subset_1(sK0,sK2)),sK0)
    | ~ spl7_22
    | ~ spl7_35 ),
    inference(resolution,[],[f676,f72])).

fof(f676,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k3_subset_1(sK0,sK2))
        | r2_hidden(X6,sK0) )
    | ~ spl7_22
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f675,f401])).

fof(f401,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f400])).

fof(f675,plain,
    ( ! [X6] :
        ( v1_xboole_0(k3_subset_1(sK0,sK2))
        | ~ m1_subset_1(X6,k3_subset_1(sK0,sK2))
        | r2_hidden(X6,sK0) )
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f669,f294])).

fof(f669,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k3_subset_1(sK0,sK2))
        | v1_xboole_0(k4_xboole_0(sK0,sK2))
        | r2_hidden(X6,sK0) )
    | ~ spl7_22 ),
    inference(superposition,[],[f165,f294])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k4_xboole_0(X1,X2))
      | v1_xboole_0(k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f76,f71])).

fof(f9258,plain,
    ( ~ spl7_157
    | ~ spl7_22
    | spl7_35 ),
    inference(avatar_split_clause,[],[f3946,f400,f293,f9256])).

fof(f9256,plain,
    ( spl7_157
  <=> ~ r2_hidden(sK6(k3_subset_1(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_157])])).

fof(f3946,plain,
    ( ~ r2_hidden(sK6(k3_subset_1(sK0,sK2)),sK2)
    | ~ spl7_22
    | ~ spl7_35 ),
    inference(resolution,[],[f639,f72])).

fof(f639,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X6,sK2) )
    | ~ spl7_22
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f638,f401])).

fof(f638,plain,
    ( ! [X6] :
        ( v1_xboole_0(k3_subset_1(sK0,sK2))
        | ~ m1_subset_1(X6,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X6,sK2) )
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f633,f294])).

fof(f633,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k3_subset_1(sK0,sK2))
        | v1_xboole_0(k4_xboole_0(sK0,sK2))
        | ~ r2_hidden(X6,sK2) )
    | ~ spl7_22 ),
    inference(superposition,[],[f148,f294])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k4_xboole_0(X2,X1))
      | v1_xboole_0(k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f75,f71])).

fof(f8550,plain,
    ( spl7_154
    | spl7_54 ),
    inference(avatar_split_clause,[],[f672,f1657,f8548])).

fof(f672,plain,(
    ! [X1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f671,f59])).

fof(f671,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_xboole_0)
      | v1_xboole_0(k4_xboole_0(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f666,f150])).

fof(f666,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_xboole_0)
      | v1_xboole_0(k4_xboole_0(k1_xboole_0,X0))
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f165,f59])).

fof(f8546,plain,
    ( spl7_152
    | ~ spl7_0
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f8515,f300,f86,f8544])).

fof(f86,plain,
    ( spl7_0
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f8515,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl7_0
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f8514,f273])).

fof(f273,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(sK2,X7),sK0)
        | r1_tarski(sK2,X7) )
    | ~ spl7_0 ),
    inference(resolution,[],[f189,f64])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,sK0) )
    | ~ spl7_0 ),
    inference(resolution,[],[f66,f87])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f86])).

fof(f8514,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ r2_hidden(sK5(sK2,k3_subset_1(sK0,sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f8499])).

fof(f8499,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ r2_hidden(sK5(sK2,k3_subset_1(sK0,sK1)),sK0)
    | r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl7_0
    | ~ spl7_24 ),
    inference(resolution,[],[f951,f4898])).

fof(f4898,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,X0),sK1)
        | r1_tarski(sK2,X0) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f127,f3848])).

fof(f3848,plain,
    ( ! [X2] :
        ( r1_tarski(sK2,X2)
        | m1_subset_1(sK5(sK2,X2),sK0) )
    | ~ spl7_0 ),
    inference(resolution,[],[f273,f81])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,X0),sK1)
      | ~ m1_subset_1(sK5(sK2,X0),sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f64,f38])).

fof(f951,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(X7,k3_subset_1(sK0,sK1)),sK1)
        | r1_tarski(X7,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(sK5(X7,k3_subset_1(sK0,sK1)),sK0) )
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f950,f301])).

fof(f950,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(X7,k3_subset_1(sK0,sK1)),sK1)
        | ~ r2_hidden(sK5(X7,k3_subset_1(sK0,sK1)),sK0)
        | r1_tarski(X7,k4_xboole_0(sK0,sK1)) )
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f938,f301])).

fof(f938,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK5(X7,k3_subset_1(sK0,sK1)),sK0)
        | r2_hidden(sK5(X7,k4_xboole_0(sK0,sK1)),sK1)
        | r1_tarski(X7,k4_xboole_0(sK0,sK1)) )
    | ~ spl7_24 ),
    inference(superposition,[],[f223,f301])).

fof(f223,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(sK5(X17,k4_xboole_0(X18,X19)),X18)
      | r2_hidden(sK5(X17,k4_xboole_0(X18,X19)),X19)
      | r1_tarski(X17,k4_xboole_0(X18,X19)) ) ),
    inference(resolution,[],[f74,f65])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f8498,plain,
    ( spl7_150
    | ~ spl7_101
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f528,f466,f4800,f8496])).

fof(f8496,plain,
    ( spl7_150
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f4800,plain,
    ( spl7_101
  <=> ~ r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f466,plain,
    ( spl7_36
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f528,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl7_36 ),
    inference(resolution,[],[f467,f55])).

fof(f467,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f466])).

fof(f8366,plain,
    ( ~ spl7_149
    | spl7_21
    | spl7_85 ),
    inference(avatar_split_clause,[],[f7334,f4012,f206,f8364])).

fof(f8364,plain,
    ( spl7_149
  <=> ~ m1_subset_1(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).

fof(f206,plain,
    ( spl7_21
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f4012,plain,
    ( spl7_85
  <=> ~ r2_hidden(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f7334,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_21
    | ~ spl7_85 ),
    inference(subsumption_resolution,[],[f7332,f207])).

fof(f207,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f7332,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_85 ),
    inference(resolution,[],[f4013,f71])).

fof(f4013,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f4012])).

fof(f8328,plain,
    ( ~ spl7_21
    | spl7_146 ),
    inference(avatar_split_clause,[],[f416,f8326,f206])).

fof(f8326,plain,
    ( spl7_146
  <=> ! [X11,X12] :
        ( r2_hidden(sK3(X11,sK2,X12),X12)
        | k4_xboole_0(X11,sK2) = X12
        | ~ m1_subset_1(sK3(X11,sK2,X12),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f416,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK3(X11,sK2,X12),X12)
      | ~ m1_subset_1(sK3(X11,sK2,X12),sK0)
      | k4_xboole_0(X11,sK2) = X12
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f257,f62])).

fof(f257,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK3(X14,sK2,X15),sK1)
      | r2_hidden(sK3(X14,sK2,X15),X15)
      | ~ m1_subset_1(sK3(X14,sK2,X15),sK0)
      | k4_xboole_0(X14,sK2) = X15 ) ),
    inference(resolution,[],[f44,f37])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f8225,plain,
    ( ~ spl7_21
    | ~ spl7_145
    | spl7_41 ),
    inference(avatar_split_clause,[],[f3959,f601,f8223,f206])).

fof(f8223,plain,
    ( spl7_145
  <=> ~ v1_xboole_0(sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f601,plain,
    ( spl7_41
  <=> ~ m1_subset_1(sK6(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f3959,plain,
    ( ~ v1_xboole_0(sK6(sK2))
    | ~ v1_xboole_0(sK1)
    | ~ spl7_41 ),
    inference(resolution,[],[f602,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f602,plain,
    ( ~ m1_subset_1(sK6(sK2),sK1)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f601])).

fof(f8041,plain,
    ( spl7_142
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f8005,f7863,f8039])).

fof(f8039,plain,
    ( spl7_142
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f7863,plain,
    ( spl7_140
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f8005,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_140 ),
    inference(superposition,[],[f72,f7864])).

fof(f7864,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f7863])).

fof(f7865,plain,
    ( spl7_140
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f7655,f2206,f7863])).

fof(f7655,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_58 ),
    inference(resolution,[],[f2589,f2232])).

fof(f2589,plain,
    ( ! [X26,X25] :
        ( r2_hidden(sK3(X25,X25,sK6(k1_zfmisc_1(X26))),X26)
        | k1_xboole_0 = sK6(k1_zfmisc_1(X26)) )
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2565,f620])).

fof(f620,plain,(
    ! [X26,X25] :
      ( k4_xboole_0(X25,X25) = sK6(k1_zfmisc_1(X26))
      | r2_hidden(sK3(X25,X25,sK6(k1_zfmisc_1(X26))),X26) ) ),
    inference(resolution,[],[f258,f192])).

fof(f192,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK6(k1_zfmisc_1(X6)))
      | r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f66,f72])).

fof(f258,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f44,f43])).

fof(f2565,plain,
    ( ! [X24] : k4_xboole_0(X24,X24) = k1_xboole_0
    | ~ spl7_58 ),
    inference(resolution,[],[f258,f2232])).

fof(f7669,plain,
    ( spl7_138
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f7662,f2206,f7667])).

fof(f7667,plain,
    ( spl7_138
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f7662,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f7655,f542])).

fof(f542,plain,(
    k3_subset_1(k1_xboole_0,sK6(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[],[f197,f59])).

fof(f197,plain,(
    ! [X2] : k3_subset_1(X2,sK6(k1_zfmisc_1(X2))) = k4_xboole_0(X2,sK6(k1_zfmisc_1(X2))) ),
    inference(resolution,[],[f56,f72])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',d5_subset_1)).

fof(f7598,plain,
    ( spl7_136
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f7397,f300,f7596])).

fof(f7596,plain,
    ( spl7_136
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f7397,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f7390])).

fof(f7390,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl7_24 ),
    inference(resolution,[],[f708,f65])).

fof(f7501,plain,
    ( spl7_134
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f7389,f293,f7499])).

fof(f7499,plain,
    ( spl7_134
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f7389,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | ~ spl7_22 ),
    inference(duplicate_literal_removal,[],[f7382])).

fof(f7382,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f707,f65])).

fof(f707,plain,
    ( ! [X6] :
        ( r2_hidden(sK5(k3_subset_1(sK0,sK2),X6),sK0)
        | r1_tarski(k3_subset_1(sK0,sK2),X6) )
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f696,f294])).

fof(f696,plain,
    ( ! [X6] :
        ( r2_hidden(sK5(k3_subset_1(sK0,sK2),X6),sK0)
        | r1_tarski(k4_xboole_0(sK0,sK2),X6) )
    | ~ spl7_22 ),
    inference(superposition,[],[f166,f294])).

fof(f7329,plain,
    ( spl7_132
    | spl7_118
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f677,f300,f7048,f7327])).

fof(f677,plain,
    ( ! [X7] :
        ( v1_xboole_0(k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | r2_hidden(X7,sK0) )
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f670,f301])).

fof(f670,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | v1_xboole_0(k4_xboole_0(sK0,sK1))
        | r2_hidden(X7,sK0) )
    | ~ spl7_24 ),
    inference(superposition,[],[f165,f301])).

fof(f7298,plain,
    ( spl7_130
    | spl7_118
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f640,f300,f7048,f7296])).

fof(f640,plain,
    ( ! [X7] :
        ( v1_xboole_0(k3_subset_1(sK0,sK1))
        | ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X7,sK1) )
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f634,f301])).

fof(f634,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k3_subset_1(sK0,sK1))
        | v1_xboole_0(k4_xboole_0(sK0,sK1))
        | ~ r2_hidden(X7,sK1) )
    | ~ spl7_24 ),
    inference(superposition,[],[f148,f301])).

fof(f7272,plain,
    ( ~ spl7_129
    | spl7_21
    | spl7_125 ),
    inference(avatar_split_clause,[],[f7160,f7076,f206,f7270])).

fof(f7270,plain,
    ( spl7_129
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f7076,plain,
    ( spl7_125
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f7160,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK1)
    | ~ spl7_21
    | ~ spl7_125 ),
    inference(subsumption_resolution,[],[f7158,f207])).

fof(f7158,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_zfmisc_1(sK0),sK1)
    | ~ spl7_125 ),
    inference(resolution,[],[f7077,f71])).

fof(f7077,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK1)
    | ~ spl7_125 ),
    inference(avatar_component_clause,[],[f7076])).

fof(f7234,plain,
    ( ~ spl7_127
    | ~ spl7_36
    | spl7_125 ),
    inference(avatar_split_clause,[],[f7159,f7076,f466,f7232])).

fof(f7232,plain,
    ( spl7_127
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).

fof(f7159,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK0)
    | ~ spl7_36
    | ~ spl7_125 ),
    inference(subsumption_resolution,[],[f7155,f467])).

fof(f7155,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK0)
    | ~ r1_tarski(sK2,sK0)
    | ~ spl7_125 ),
    inference(resolution,[],[f7077,f133])).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(k1_zfmisc_1(X0),sK1)
      | ~ m1_subset_1(k1_zfmisc_1(X0),sK0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',d1_zfmisc_1)).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ m1_subset_1(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f67,f37])).

fof(f7078,plain,
    ( ~ spl7_125
    | ~ spl7_0
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f7063,f179,f86,f7076])).

fof(f179,plain,
    ( spl7_16
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f7063,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK1)
    | ~ spl7_0
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f7062,f87])).

fof(f7062,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f7056,f73])).

fof(f73,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',fc1_subset_1)).

fof(f7056,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK1)
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_16 ),
    inference(resolution,[],[f1775,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',dt_k3_subset_1)).

fof(f1775,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_subset_1(sK0,sK2),X1)
        | ~ r2_hidden(X1,sK1)
        | v1_xboole_0(X1) )
    | ~ spl7_16 ),
    inference(resolution,[],[f1675,f141])).

fof(f141,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X4,X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f71,f67])).

fof(f1675,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_16 ),
    inference(resolution,[],[f180,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f180,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f7071,plain,
    ( ~ spl7_21
    | spl7_122 ),
    inference(avatar_split_clause,[],[f5095,f7069,f206])).

fof(f7069,plain,
    ( spl7_122
  <=> ! [X6] :
        ( ~ m1_subset_1(sK5(X6,sK2),sK0)
        | r1_tarski(X6,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f5095,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK5(X6,sK2),sK0)
      | r1_tarski(X6,sK2)
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f136,f62])).

fof(f7067,plain,
    ( spl7_20
    | spl7_120
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f4602,f86,f7065,f209])).

fof(f7065,plain,
    ( spl7_120
  <=> ! [X1] :
        ( r1_tarski(sK2,X1)
        | ~ m1_subset_1(sK5(sK2,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f4602,plain,
    ( ! [X1] :
        ( r1_tarski(sK2,X1)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK5(sK2,X1),sK1) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f364,f3848])).

fof(f364,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5(sK2,X1),sK0)
      | r1_tarski(sK2,X1)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK5(sK2,X1),sK1) ) ),
    inference(resolution,[],[f127,f71])).

fof(f7053,plain,
    ( spl7_116
    | ~ spl7_119
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f539,f300,f7051,f7045])).

fof(f7045,plain,
    ( spl7_116
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK0)
        | r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f7051,plain,
    ( spl7_119
  <=> ~ v1_xboole_0(k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f539,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(k3_subset_1(sK0,sK1))
        | ~ r2_hidden(X5,sK0)
        | r2_hidden(X5,sK1) )
    | ~ spl7_24 ),
    inference(superposition,[],[f221,f301])).

fof(f221,plain,(
    ! [X14,X12,X13] :
      ( ~ v1_xboole_0(k4_xboole_0(X14,X13))
      | ~ r2_hidden(X12,X14)
      | r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f74,f62])).

fof(f7043,plain,
    ( spl7_88
    | spl7_114
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f4971,f2966,f2206,f1818,f7041,f4037])).

fof(f4037,plain,
    ( spl7_88
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f7041,plain,
    ( spl7_114
  <=> ! [X22] : ~ m1_subset_1(sK3(X22,X22,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f1818,plain,
    ( spl7_56
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f2966,plain,
    ( spl7_72
  <=> ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ m1_subset_1(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f4971,plain,
    ( ! [X22] :
        ( ~ m1_subset_1(sK3(X22,X22,sK1),sK2)
        | k1_xboole_0 = sK1 )
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_72 ),
    inference(resolution,[],[f4899,f2578])).

fof(f2578,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X2,X3),X3)
        | k1_xboole_0 = X3 )
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2565,f258])).

fof(f4899,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl7_56
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f1819,f3769])).

fof(f3769,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | m1_subset_1(X1,sK0) )
    | ~ spl7_72 ),
    inference(resolution,[],[f2967,f81])).

fof(f2967,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f2966])).

fof(f1819,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f1818])).

fof(f7037,plain,
    ( spl7_88
    | spl7_86
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f4952,f2206,f93,f4031,f4037])).

fof(f4031,plain,
    ( spl7_86
  <=> ! [X22] : r2_hidden(sK3(X22,X22,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f93,plain,
    ( spl7_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f4952,plain,
    ( ! [X22] :
        ( r2_hidden(sK3(X22,X22,sK1),sK0)
        | k1_xboole_0 = sK1 )
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(resolution,[],[f190,f2578])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f66,f94])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f7011,plain,
    ( ~ spl7_21
    | spl7_112 ),
    inference(avatar_split_clause,[],[f5068,f7009,f206])).

fof(f7009,plain,
    ( spl7_112
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK0)
        | m1_subset_1(X5,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f5068,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | m1_subset_1(X5,sK2)
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f107,f62])).

fof(f7003,plain,
    ( spl7_20
    | spl7_110
    | ~ spl7_56
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f4915,f2966,f1818,f7001,f209])).

fof(f7001,plain,
    ( spl7_110
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f4915,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_56
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f3619,f3769])).

fof(f3619,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_56 ),
    inference(resolution,[],[f1819,f71])).

fof(f6923,plain,
    ( spl7_108
    | ~ spl7_2
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f6582,f3422,f93,f6921])).

fof(f6921,plain,
    ( spl7_108
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f3422,plain,
    ( spl7_74
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f6582,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl7_2
    | ~ spl7_74 ),
    inference(resolution,[],[f3423,f190])).

fof(f3423,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f3422])).

fof(f6866,plain,
    ( ~ spl7_107
    | ~ spl7_56
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f6581,f3422,f2966,f1818,f6864])).

fof(f6864,plain,
    ( spl7_107
  <=> ~ m1_subset_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f6581,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK2)
    | ~ spl7_56
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(resolution,[],[f3423,f4899])).

fof(f6326,plain,
    ( ~ spl7_21
    | spl7_103 ),
    inference(avatar_split_clause,[],[f5127,f5124,f206])).

fof(f5124,plain,
    ( spl7_103
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f5127,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_103 ),
    inference(resolution,[],[f5125,f130])).

fof(f5125,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f5124])).

fof(f6297,plain,
    ( ~ spl7_36
    | ~ spl7_62
    | spl7_97
    | ~ spl7_100 ),
    inference(avatar_contradiction_clause,[],[f6296])).

fof(f6296,plain,
    ( $false
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_97
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f6295,f704])).

fof(f6295,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_97
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f5976,f2315])).

fof(f2315,plain,
    ( k3_subset_1(sK0,sK0) = k1_xboole_0
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f2314])).

fof(f2314,plain,
    ( spl7_62
  <=> k3_subset_1(sK0,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f5976,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),k1_xboole_0)
    | ~ spl7_36
    | ~ spl7_97
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f5860,f4685])).

fof(f5860,plain,
    ( sK0 = sK2
    | ~ spl7_36
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f5859,f467])).

fof(f5859,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2
    | ~ spl7_100 ),
    inference(resolution,[],[f4804,f55])).

fof(f4804,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f4803])).

fof(f4803,plain,
    ( spl7_100
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f6294,plain,
    ( ~ spl7_36
    | ~ spl7_62
    | spl7_95
    | ~ spl7_100 ),
    inference(avatar_contradiction_clause,[],[f6293])).

fof(f6293,plain,
    ( $false
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_95
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f5975,f2315])).

fof(f5975,plain,
    ( k3_subset_1(sK0,sK0) != k1_xboole_0
    | ~ spl7_36
    | ~ spl7_95
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f5860,f4678])).

fof(f6288,plain,
    ( ~ spl7_22
    | spl7_35
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(avatar_contradiction_clause,[],[f6287])).

fof(f6287,plain,
    ( $false
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f6286,f6285])).

fof(f6285,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0),sK0)
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f5969,f2315])).

fof(f5969,plain,
    ( ~ r2_hidden(sK6(k3_subset_1(sK0,sK0)),sK0)
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f5860,f3946])).

fof(f6286,plain,
    ( r2_hidden(sK6(k1_xboole_0),sK0)
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f5970,f2315])).

fof(f5970,plain,
    ( r2_hidden(sK6(k3_subset_1(sK0,sK0)),sK0)
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f5860,f3952])).

fof(f6027,plain,
    ( spl7_35
    | ~ spl7_36
    | ~ spl7_54
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(avatar_contradiction_clause,[],[f6026])).

fof(f6026,plain,
    ( $false
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_54
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(subsumption_resolution,[],[f6025,f1658])).

fof(f6025,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_62
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f5873,f2315])).

fof(f5873,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK0))
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_100 ),
    inference(backward_demodulation,[],[f5860,f401])).

fof(f5811,plain,
    ( ~ spl7_54
    | ~ spl7_88
    | spl7_103 ),
    inference(avatar_contradiction_clause,[],[f5810])).

fof(f5810,plain,
    ( $false
    | ~ spl7_54
    | ~ spl7_88
    | ~ spl7_103 ),
    inference(subsumption_resolution,[],[f5497,f1658])).

fof(f5497,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_88
    | ~ spl7_103 ),
    inference(backward_demodulation,[],[f4038,f5127])).

fof(f4038,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f4037])).

fof(f5809,plain,
    ( ~ spl7_88
    | spl7_103 ),
    inference(avatar_contradiction_clause,[],[f5808])).

fof(f5808,plain,
    ( $false
    | ~ spl7_88
    | ~ spl7_103 ),
    inference(subsumption_resolution,[],[f5496,f704])).

fof(f5496,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_88
    | ~ spl7_103 ),
    inference(backward_demodulation,[],[f4038,f5125])).

fof(f5279,plain,
    ( spl7_20
    | spl7_104
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f276,f93,f5277,f209])).

fof(f276,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f190,f71])).

fof(f5201,plain,
    ( spl7_38
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f4858,f93,f499])).

fof(f499,plain,
    ( spl7_38
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f4858,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f94,f147])).

fof(f147,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | r1_tarski(X8,X7) ) ),
    inference(subsumption_resolution,[],[f143,f73])).

fof(f143,plain,(
    ! [X8,X7] :
      ( v1_xboole_0(k1_zfmisc_1(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | r1_tarski(X8,X7) ) ),
    inference(resolution,[],[f71,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5126,plain,
    ( ~ spl7_103
    | spl7_89 ),
    inference(avatar_split_clause,[],[f5119,f4034,f5124])).

fof(f4034,plain,
    ( spl7_89
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f5119,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f5117,f704])).

fof(f5117,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl7_89 ),
    inference(extensionality_resolution,[],[f55,f4035])).

fof(f4035,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f4034])).

fof(f4921,plain,
    ( ~ spl7_21
    | ~ spl7_54
    | spl7_83 ),
    inference(avatar_split_clause,[],[f4040,f3842,f1657,f206])).

fof(f3842,plain,
    ( spl7_83
  <=> ~ m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f4040,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_54
    | ~ spl7_83 ),
    inference(subsumption_resolution,[],[f3882,f1658])).

fof(f3882,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(sK1)
    | ~ spl7_83 ),
    inference(resolution,[],[f3843,f68])).

fof(f3843,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f3842])).

fof(f4897,plain,
    ( ~ spl7_20
    | spl7_89 ),
    inference(avatar_contradiction_clause,[],[f4896])).

fof(f4896,plain,
    ( $false
    | ~ spl7_20
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f4866,f4035])).

fof(f4866,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_20 ),
    inference(resolution,[],[f210,f58])).

fof(f210,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f4805,plain,
    ( spl7_100
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4751,f4037,f2206,f4803])).

fof(f4751,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(duplicate_literal_removal,[],[f4749])).

fof(f4749,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(resolution,[],[f4266,f128])).

fof(f128,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK5(X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f64,f81])).

fof(f4266,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(X1,sK2),sK0)
        | r1_tarski(X1,sK2) )
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f4058,f2232])).

fof(f4058,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(X1,sK2),k1_xboole_0)
        | ~ m1_subset_1(sK5(X1,sK2),sK0)
        | r1_tarski(X1,sK2) )
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f136])).

fof(f4748,plain,
    ( ~ spl7_99
    | spl7_19
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4064,f4037,f203,f4746])).

fof(f4746,plain,
    ( spl7_99
  <=> ~ m1_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f203,plain,
    ( spl7_19
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f4064,plain,
    ( ~ m1_subset_1(sK2,k1_xboole_0)
    | ~ spl7_19
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f204])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f4723,plain,
    ( ~ spl7_6
    | spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88
    | spl7_93 ),
    inference(avatar_contradiction_clause,[],[f4722])).

fof(f4722,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88
    | ~ spl7_93 ),
    inference(subsumption_resolution,[],[f4716,f4668])).

fof(f4668,plain,
    ( k1_xboole_0 != sK0
    | ~ spl7_93 ),
    inference(avatar_component_clause,[],[f4667])).

fof(f4667,plain,
    ( spl7_93
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f4716,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(resolution,[],[f4662,f2580])).

fof(f2580,plain,
    ( ! [X6,X5] :
        ( m1_subset_1(sK3(X5,X5,X6),X6)
        | k1_xboole_0 = X6 )
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2565,f609])).

fof(f609,plain,(
    ! [X6,X5] :
      ( k4_xboole_0(X5,X5) = X6
      | m1_subset_1(sK3(X5,X5,X6),X6) ) ),
    inference(resolution,[],[f258,f81])).

fof(f4662,plain,
    ( ! [X2] : ~ m1_subset_1(X2,sK0)
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f4661,f4647])).

fof(f4647,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_xboole_0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f4646,f4038])).

fof(f4646,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2450,f4264])).

fof(f4264,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK2)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f4055,f2232])).

fof(f4055,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,sK0)
        | m1_subset_1(X0,sK2) )
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f107])).

fof(f2450,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_21
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f2431,f207])).

fof(f2431,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_56 ),
    inference(resolution,[],[f1819,f71])).

fof(f4661,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,sK0) )
    | ~ spl7_6
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f3404,f4038])).

fof(f3404,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | m1_subset_1(X2,sK1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f110,f81])).

fof(f110,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f4721,plain,
    ( ~ spl7_6
    | spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88
    | spl7_93 ),
    inference(avatar_contradiction_clause,[],[f4720])).

fof(f4720,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88
    | ~ spl7_93 ),
    inference(subsumption_resolution,[],[f4715,f4668])).

fof(f4715,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(resolution,[],[f4662,f2293])).

fof(f2293,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK3(k1_xboole_0,X8,X9),X9)
        | k1_xboole_0 = X9 )
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f2280,f59])).

fof(f2280,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK3(k1_xboole_0,X8,X9),X9)
        | k4_xboole_0(k1_xboole_0,X8) = X9 )
    | ~ spl7_58 ),
    inference(resolution,[],[f2232,f237])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | m1_subset_1(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(resolution,[],[f43,f81])).

fof(f4719,plain,
    ( ~ spl7_6
    | spl7_21
    | ~ spl7_48
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f4709])).

fof(f4709,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_48
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(resolution,[],[f4662,f1316])).

fof(f1316,plain,
    ( m1_subset_1(sK6(sK2),sK0)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1315,plain,
    ( spl7_48
  <=> m1_subset_1(sK6(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f4718,plain,
    ( ~ spl7_6
    | spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f4710])).

fof(f4710,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_21
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(resolution,[],[f4662,f72])).

fof(f4686,plain,
    ( ~ spl7_97
    | spl7_15
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4061,f4037,f176,f4684])).

fof(f4061,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k1_xboole_0)
    | ~ spl7_15
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f177])).

fof(f177,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f4679,plain,
    ( ~ spl7_95
    | spl7_5
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4053,f4037,f100,f4677])).

fof(f4053,plain,
    ( k3_subset_1(sK0,sK2) != k1_xboole_0
    | ~ spl7_5
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f101])).

fof(f4669,plain,
    ( ~ spl7_93
    | spl7_53
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4158,f4037,f1650,f4667])).

fof(f4158,plain,
    ( k1_xboole_0 != sK0
    | ~ spl7_53
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f1651])).

fof(f4659,plain,
    ( ~ spl7_91
    | spl7_51
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4157,f4037,f1643,f4657])).

fof(f4657,plain,
    ( spl7_91
  <=> ~ r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f1643,plain,
    ( spl7_51
  <=> ~ r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f4157,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl7_51
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f1644])).

fof(f1644,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f4652,plain,
    ( ~ spl7_55
    | spl7_83
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f4636,f4037,f3842,f1654])).

fof(f1654,plain,
    ( spl7_55
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f4636,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_83
    | ~ spl7_88 ),
    inference(duplicate_literal_removal,[],[f4635])).

fof(f4635,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_83
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f3882,f4038])).

fof(f4595,plain,
    ( ~ spl7_54
    | spl7_83
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f4594])).

fof(f4594,plain,
    ( $false
    | ~ spl7_54
    | ~ spl7_83
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f4255,f1658])).

fof(f4255,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_54
    | ~ spl7_83
    | ~ spl7_88 ),
    inference(backward_demodulation,[],[f4038,f4040])).

fof(f4039,plain,
    ( spl7_86
    | spl7_88
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f2586,f2206,f93,f4037,f4031])).

fof(f2586,plain,
    ( ! [X22] :
        ( k1_xboole_0 = sK1
        | r2_hidden(sK3(X22,X22,sK1),sK0) )
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2565,f617])).

fof(f617,plain,
    ( ! [X22] :
        ( k4_xboole_0(X22,X22) = sK1
        | r2_hidden(sK3(X22,X22,sK1),sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f258,f190])).

fof(f4014,plain,
    ( ~ spl7_85
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f3974,f179,f4012])).

fof(f3974,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_16 ),
    inference(duplicate_literal_removal,[],[f3967])).

fof(f3967,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),sK1)
    | ~ r2_hidden(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f1777,f1675])).

fof(f1777,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k3_subset_1(sK0,sK2),X3)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl7_16 ),
    inference(resolution,[],[f1675,f67])).

fof(f3844,plain,
    ( ~ spl7_83
    | spl7_21
    | spl7_75 ),
    inference(avatar_split_clause,[],[f3642,f3425,f206,f3842])).

fof(f3425,plain,
    ( spl7_75
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f3642,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl7_21
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f3641,f207])).

fof(f3641,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl7_75 ),
    inference(resolution,[],[f3426,f71])).

fof(f3426,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f3425])).

fof(f3759,plain,
    ( ~ spl7_81
    | spl7_79 ),
    inference(avatar_split_clause,[],[f3752,f3436,f3757])).

fof(f3752,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_79 ),
    inference(subsumption_resolution,[],[f3750,f704])).

fof(f3750,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_79 ),
    inference(extensionality_resolution,[],[f55,f3437])).

fof(f3639,plain,
    ( spl7_8
    | spl7_56 ),
    inference(avatar_split_clause,[],[f2256,f1818,f112])).

fof(f112,plain,
    ( spl7_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f2256,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X1,sK2) ) ),
    inference(resolution,[],[f38,f71])).

fof(f3586,plain,
    ( ~ spl7_9
    | spl7_6 ),
    inference(avatar_split_clause,[],[f2243,f109,f115])).

fof(f115,plain,
    ( spl7_9
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f2243,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK1)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f37,f62])).

fof(f3441,plain,
    ( spl7_78
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f3007,f2206,f112,f86,f3439])).

fof(f3439,plain,
    ( spl7_78
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f3007,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(global_subsumption,[],[f1828])).

fof(f1828,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(resolution,[],[f113,f58])).

fof(f113,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f3434,plain,
    ( ~ spl7_77
    | ~ spl7_8
    | spl7_13 ),
    inference(avatar_split_clause,[],[f1333,f162,f112,f3432])).

fof(f3432,plain,
    ( spl7_77
  <=> ~ m1_subset_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f162,plain,
    ( spl7_13
  <=> ~ m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f1333,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f1319,f163])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f1319,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(resolution,[],[f113,f58])).

fof(f3427,plain,
    ( ~ spl7_75
    | ~ spl7_8
    | spl7_11 ),
    inference(avatar_split_clause,[],[f1332,f153,f112,f3425])).

fof(f153,plain,
    ( spl7_11
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1332,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f1319,f154])).

fof(f154,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2968,plain,
    ( spl7_8
    | spl7_72
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f269,f86,f2966,f112])).

fof(f269,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl7_0 ),
    inference(resolution,[],[f189,f71])).

fof(f2858,plain,
    ( spl7_70
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f808,f324,f93,f2856])).

fof(f808,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f800,f325])).

fof(f800,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl7_2 ),
    inference(resolution,[],[f196,f94])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f56,f61])).

fof(f2851,plain,
    ( spl7_68
    | ~ spl7_0
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f807,f307,f86,f2849])).

fof(f2849,plain,
    ( spl7_68
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f307,plain,
    ( spl7_26
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f807,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl7_0
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f799,f308])).

fof(f308,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f307])).

fof(f799,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl7_0 ),
    inference(resolution,[],[f196,f87])).

fof(f2783,plain,
    ( spl7_66
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f2230,f2206,f2781])).

fof(f2781,plain,
    ( spl7_66
  <=> k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f2230,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2229,f2228])).

fof(f2228,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,k1_xboole_0)) = k1_xboole_0
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2224,f2222])).

fof(f2222,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl7_58 ),
    inference(resolution,[],[f2207,f196])).

fof(f2224,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0)) = k1_xboole_0
    | ~ spl7_58 ),
    inference(resolution,[],[f2207,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t51_subset_1.p',involutiveness_k3_subset_1)).

fof(f2229,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f2225,f60])).

fof(f2225,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl7_58 ),
    inference(resolution,[],[f2207,f56])).

fof(f2668,plain,
    ( spl7_64
    | ~ spl7_58
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f2319,f2307,f2206,f2666])).

fof(f2666,plain,
    ( spl7_64
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f2319,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl7_58
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f2318,f2207])).

fof(f2318,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl7_60 ),
    inference(superposition,[],[f61,f2308])).

fof(f2401,plain,
    ( ~ spl7_9
    | spl7_6 ),
    inference(avatar_split_clause,[],[f1680,f109,f115])).

fof(f1680,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK1)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f37,f62])).

fof(f2316,plain,
    ( spl7_62
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f2231,f2206,f2314])).

fof(f2231,plain,
    ( k3_subset_1(sK0,sK0) = k1_xboole_0
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f2229,f2224])).

fof(f2309,plain,
    ( spl7_60
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f2229,f2206,f2307])).

fof(f2220,plain,(
    spl7_59 ),
    inference(avatar_contradiction_clause,[],[f2219])).

fof(f2219,plain,
    ( $false
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f2217,f704])).

fof(f2217,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_59 ),
    inference(resolution,[],[f2204,f124])).

fof(f124,plain,(
    ! [X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f78,f81])).

fof(f2204,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f2203])).

fof(f2203,plain,
    ( spl7_59
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f2208,plain,
    ( spl7_58
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f1322,f112,f86,f2206])).

fof(f1322,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f1319,f87])).

fof(f1820,plain,
    ( spl7_56
    | spl7_8 ),
    inference(avatar_split_clause,[],[f139,f112,f1818])).

fof(f139,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f71,f38])).

fof(f1659,plain,
    ( spl7_54
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f1326,f112,f1657])).

fof(f1326,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f1319,f113])).

fof(f1652,plain,
    ( ~ spl7_53
    | spl7_5
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f1464,f293,f112,f100,f1650])).

fof(f1464,plain,
    ( sK0 != sK1
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f1461,f1323])).

fof(f1323,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f1319,f101])).

fof(f1461,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f1347,f60])).

fof(f1347,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f1319,f294])).

fof(f1645,plain,
    ( ~ spl7_51
    | ~ spl7_8
    | spl7_15
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f1463,f293,f176,f112,f1643])).

fof(f1463,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f1461,f1334])).

fof(f1334,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k1_xboole_0),sK1)
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f1319,f177])).

fof(f1466,plain,
    ( ~ spl7_8
    | spl7_17
    | ~ spl7_22
    | ~ spl7_38 ),
    inference(avatar_contradiction_clause,[],[f1465])).

fof(f1465,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_17
    | ~ spl7_22
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1462,f500])).

fof(f500,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f499])).

fof(f1462,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl7_8
    | ~ spl7_17
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f1461,f1335])).

fof(f1335,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f1319,f183])).

fof(f183,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1317,plain,
    ( spl7_48
    | ~ spl7_0
    | spl7_9 ),
    inference(avatar_split_clause,[],[f1155,f115,f86,f1315])).

fof(f1155,plain,
    ( m1_subset_1(sK6(sK2),sK0)
    | ~ spl7_0
    | ~ spl7_9 ),
    inference(resolution,[],[f344,f72])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | m1_subset_1(X0,sK0) )
    | ~ spl7_0
    | ~ spl7_9 ),
    inference(resolution,[],[f275,f81])).

fof(f275,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl7_0
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f269,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f885,plain,
    ( ~ spl7_47
    | ~ spl7_0
    | ~ spl7_2
    | spl7_9 ),
    inference(avatar_split_clause,[],[f731,f115,f93,f86,f883])).

fof(f883,plain,
    ( spl7_47
  <=> ~ m1_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f731,plain,
    ( ~ m1_subset_1(sK0,sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f725,f344])).

fof(f725,plain,
    ( ~ m1_subset_1(sK0,sK0)
    | ~ m1_subset_1(sK0,sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(resolution,[],[f283,f275])).

fof(f283,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(resolution,[],[f274,f67])).

fof(f274,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f268,f190])).

fof(f268,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl7_0 ),
    inference(resolution,[],[f189,f37])).

fof(f824,plain,
    ( ~ spl7_45
    | ~ spl7_0
    | ~ spl7_2
    | spl7_21 ),
    inference(avatar_split_clause,[],[f730,f206,f93,f86,f822])).

fof(f822,plain,
    ( spl7_45
  <=> ~ m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f730,plain,
    ( ~ m1_subset_1(sK0,sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f724,f376])).

fof(f376,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(X0,sK0) )
    | ~ spl7_2
    | ~ spl7_21 ),
    inference(resolution,[],[f281,f81])).

fof(f281,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl7_2
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f276,f207])).

fof(f724,plain,
    ( ~ m1_subset_1(sK0,sK0)
    | ~ m1_subset_1(sK0,sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_21 ),
    inference(resolution,[],[f283,f281])).

fof(f797,plain,
    ( ~ spl7_43
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f729,f93,f86,f795])).

fof(f795,plain,
    ( spl7_43
  <=> ~ m1_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f729,plain,
    ( ~ m1_subset_1(sK0,sK0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f726])).

fof(f726,plain,
    ( ~ m1_subset_1(sK0,sK0)
    | ~ m1_subset_1(sK0,sK0)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(resolution,[],[f283,f274])).

fof(f603,plain,
    ( ~ spl7_41
    | ~ spl7_0
    | spl7_9
    | spl7_21 ),
    inference(avatar_split_clause,[],[f556,f206,f115,f86,f601])).

fof(f556,plain,
    ( ~ m1_subset_1(sK6(sK2),sK1)
    | ~ spl7_0
    | ~ spl7_9
    | ~ spl7_21 ),
    inference(resolution,[],[f359,f72])).

fof(f359,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_0
    | ~ spl7_9
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f358,f344])).

fof(f358,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK2)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_9
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f352,f207])).

fof(f352,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl7_9 ),
    inference(resolution,[],[f146,f71])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f139,f116])).

fof(f501,plain,
    ( spl7_38
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f457,f93,f499])).

fof(f457,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f147,f94])).

fof(f468,plain,
    ( spl7_36
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f456,f86,f466])).

fof(f456,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl7_0 ),
    inference(resolution,[],[f147,f87])).

fof(f402,plain,
    ( ~ spl7_35
    | spl7_15 ),
    inference(avatar_split_clause,[],[f387,f176,f400])).

fof(f387,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl7_15 ),
    inference(resolution,[],[f130,f177])).

fof(f326,plain,
    ( spl7_32
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f213,f93,f324])).

fof(f213,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl7_2 ),
    inference(resolution,[],[f57,f94])).

fof(f319,plain,
    ( ~ spl7_29
    | spl7_30
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f284,f93,f86,f317,f314])).

fof(f314,plain,
    ( spl7_29
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f317,plain,
    ( spl7_30
  <=> ! [X2] : ~ m1_subset_1(X2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f284,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ v1_xboole_0(sK0) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(resolution,[],[f274,f62])).

fof(f309,plain,
    ( spl7_26
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f212,f86,f307])).

fof(f212,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl7_0 ),
    inference(resolution,[],[f57,f87])).

fof(f302,plain,
    ( spl7_24
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f195,f93,f300])).

fof(f195,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f56,f94])).

fof(f295,plain,
    ( spl7_22
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f194,f86,f293])).

fof(f194,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl7_0 ),
    inference(resolution,[],[f56,f87])).

fof(f211,plain,
    ( ~ spl7_19
    | spl7_20
    | spl7_11 ),
    inference(avatar_split_clause,[],[f185,f153,f209,f203])).

fof(f185,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(resolution,[],[f154,f71])).

fof(f184,plain,
    ( ~ spl7_15
    | ~ spl7_17
    | spl7_5 ),
    inference(avatar_split_clause,[],[f169,f100,f182,f176])).

fof(f169,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl7_5 ),
    inference(extensionality_resolution,[],[f55,f101])).

fof(f164,plain,
    ( spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f134,f162,f156])).

fof(f156,plain,
    ( spl7_10
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f106,f37])).

fof(f117,plain,
    ( spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f105,f115,f109])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f62,f37])).

fof(f102,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f40,f100])).

fof(f40,plain,(
    k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
