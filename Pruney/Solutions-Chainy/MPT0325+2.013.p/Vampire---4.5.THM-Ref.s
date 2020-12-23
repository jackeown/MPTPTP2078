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
% DateTime   : Thu Dec  3 12:42:39 EST 2020

% Result     : Theorem 3.75s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 270 expanded)
%              Number of leaves         :   34 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  360 ( 633 expanded)
%              Number of equality atoms :  110 ( 226 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f59,f560,f838,f1362,f1369,f1371,f1596,f1749,f2411,f2830,f2938,f2967,f3119,f3120,f3379,f3751,f3781,f3794,f3872,f3877,f4197,f4291])).

fof(f4291,plain,
    ( ~ spl6_64
    | ~ spl6_74
    | spl6_103 ),
    inference(avatar_contradiction_clause,[],[f4284])).

fof(f4284,plain,
    ( $false
    | ~ spl6_64
    | ~ spl6_74
    | spl6_103 ),
    inference(resolution,[],[f3903,f3058])).

fof(f3058,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))
    | spl6_103 ),
    inference(avatar_component_clause,[],[f3056])).

fof(f3056,plain,
    ( spl6_103
  <=> r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f3903,plain,
    ( ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,X3))
    | ~ spl6_64
    | ~ spl6_74 ),
    inference(backward_demodulation,[],[f1734,f1099])).

fof(f1099,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1098,plain,
    ( spl6_64
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f1734,plain,
    ( ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(k1_xboole_0,X3))
    | ~ spl6_74 ),
    inference(resolution,[],[f1445,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1445,plain,
    ( r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1443])).

fof(f1443,plain,
    ( spl6_74
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f4197,plain,
    ( ~ spl6_103
    | spl6_43
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f4196,f1098,f658,f3056])).

fof(f658,plain,
    ( spl6_43
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f4196,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))
    | spl6_43
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f660,f1099])).

fof(f660,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f658])).

fof(f3877,plain,
    ( spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f3852,f71,f203])).

fof(f203,plain,
    ( spl6_11
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f71,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f3852,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(superposition,[],[f93,f73])).

fof(f73,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f93,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f67,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f3872,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f3836,f71,f189,f185])).

fof(f185,plain,
    ( spl6_7
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f189,plain,
    ( spl6_8
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f3836,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,k2_zfmisc_1(sK0,sK1))
        | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    | ~ spl6_5 ),
    inference(superposition,[],[f31,f73])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f3794,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f3793,f47,f71])).

fof(f47,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f3793,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f3781,plain,
    ( spl6_4
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f1079,f973,f56])).

fof(f56,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f973,plain,
    ( spl6_60
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1079,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_60 ),
    inference(superposition,[],[f60,f975])).

fof(f975,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f973])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f29,f30])).

fof(f3751,plain,
    ( ~ spl6_32
    | spl6_110 ),
    inference(avatar_contradiction_clause,[],[f3744])).

fof(f3744,plain,
    ( $false
    | ~ spl6_32
    | spl6_110 ),
    inference(resolution,[],[f2949,f3254])).

fof(f3254,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3))
    | spl6_110 ),
    inference(avatar_component_clause,[],[f3252])).

fof(f3252,plain,
    ( spl6_110
  <=> r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f2949,plain,
    ( ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK2,X3))
    | ~ spl6_32 ),
    inference(resolution,[],[f481,f39])).

fof(f481,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl6_32
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f3379,plain,
    ( ~ spl6_110
    | spl6_7
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f3378,f1067,f185,f3252])).

fof(f1067,plain,
    ( spl6_63
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f3378,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3))
    | spl6_7
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f187,f1069])).

fof(f1069,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f1067])).

fof(f187,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f185])).

fof(f3120,plain,
    ( spl6_15
    | spl6_16
    | spl6_30
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f3083,f71,f450,f349,f345])).

fof(f345,plain,
    ( spl6_15
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f349,plain,
    ( spl6_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f450,plain,
    ( spl6_30
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f3083,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK1,sK3) = X5 )
    | ~ spl6_5 ),
    inference(superposition,[],[f136,f73])).

fof(f136,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X2,X3) = X5 ) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f3119,plain,
    ( spl6_15
    | spl6_16
    | spl6_17
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f3081,f71,f353,f349,f345])).

fof(f353,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f3081,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl6_5 ),
    inference(superposition,[],[f112,f73])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X0,X1) = X4 ) ),
    inference(superposition,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2967,plain,
    ( spl6_63
    | spl6_64
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f2966,f349,f71,f1098,f1067])).

fof(f2966,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(equality_resolution,[],[f2959])).

fof(f2959,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(duplicate_literal_removal,[],[f2958])).

fof(f2958,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f314,f351])).

fof(f351,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f349])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl6_5 ),
    inference(superposition,[],[f113,f73])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k3_xboole_0(X0,X1) = X4 ) ),
    inference(superposition,[],[f37,f36])).

fof(f2938,plain,
    ( spl6_32
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f2935,f349,f480])).

fof(f2935,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f2901])).

fof(f2901,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl6_16 ),
    inference(superposition,[],[f34,f351])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2830,plain,
    ( spl6_3
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f2785,f1523,f52])).

fof(f52,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1523,plain,
    ( spl6_79
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f2785,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_79 ),
    inference(superposition,[],[f60,f1525])).

fof(f1525,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f2411,plain,
    ( spl6_60
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f2410,f353,f973])).

fof(f2410,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_17 ),
    inference(equality_resolution,[],[f354])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f353])).

fof(f1749,plain,
    ( spl6_79
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f1748,f450,f1523])).

fof(f1748,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_30 ),
    inference(equality_resolution,[],[f451])).

fof(f451,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X1 )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f450])).

fof(f1596,plain,
    ( spl6_74
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f1585,f349,f1443])).

fof(f1585,plain,
    ( r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f1580])).

fof(f1580,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_16 ),
    inference(superposition,[],[f105,f351])).

fof(f105,plain,(
    ! [X26,X27] :
      ( k1_xboole_0 != k3_xboole_0(X26,X27)
      | r1_xboole_0(X26,k3_xboole_0(X26,X27)) ) ),
    inference(superposition,[],[f75,f67])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f34,f30])).

fof(f1371,plain,
    ( spl6_1
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f1370,f216,f42])).

fof(f42,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f216,plain,
    ( spl6_13
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1370,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f218,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f218,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1369,plain,
    ( spl6_13
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f1364,f189,f216])).

fof(f1364,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f190,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f190,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1362,plain,
    ( spl6_7
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f1355])).

fof(f1355,plain,
    ( $false
    | spl6_7
    | ~ spl6_19 ),
    inference(resolution,[],[f572,f187])).

fof(f572,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
    | ~ spl6_19 ),
    inference(resolution,[],[f384,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f384,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl6_19
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f838,plain,
    ( ~ spl6_43
    | spl6_8
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f810,f203,f189,f658])).

fof(f810,plain,
    ( ! [X23] :
        ( ~ r2_hidden(X23,k2_zfmisc_1(sK0,sK1))
        | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) )
    | ~ spl6_11 ),
    inference(superposition,[],[f104,f205])).

fof(f205,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f104,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
      | ~ r1_xboole_0(X23,k3_xboole_0(X23,X24)) ) ),
    inference(superposition,[],[f65,f67])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f31,f30])).

fof(f560,plain,
    ( spl6_19
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f556,f345,f383])).

fof(f556,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl6_15 ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK3)
    | ~ spl6_15 ),
    inference(superposition,[],[f34,f347])).

fof(f347,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f345])).

fof(f59,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f24,f56,f52])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (27146)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.46  % (27146)Refutation not found, incomplete strategy% (27146)------------------------------
% 0.21/0.46  % (27146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (27146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (27146)Memory used [KB]: 6140
% 0.21/0.46  % (27146)Time elapsed: 0.045 s
% 0.21/0.46  % (27146)------------------------------
% 0.21/0.46  % (27146)------------------------------
% 0.21/0.46  % (27138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.48  % (27155)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.49  % (27154)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (27137)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27132)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (27136)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (27133)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (27135)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27156)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (27159)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (27141)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (27131)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27149)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (27150)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (27139)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (27144)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (27160)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (27151)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (27134)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (27147)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (27140)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27148)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (27143)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (27148)Refutation not found, incomplete strategy% (27148)------------------------------
% 0.21/0.54  % (27148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27148)Memory used [KB]: 10618
% 0.21/0.54  % (27148)Time elapsed: 0.141 s
% 0.21/0.54  % (27148)------------------------------
% 0.21/0.54  % (27148)------------------------------
% 0.21/0.54  % (27142)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (27152)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (27153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (27153)Refutation not found, incomplete strategy% (27153)------------------------------
% 0.21/0.55  % (27153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27153)Memory used [KB]: 10618
% 0.21/0.55  % (27153)Time elapsed: 0.136 s
% 0.21/0.55  % (27153)------------------------------
% 0.21/0.55  % (27153)------------------------------
% 0.21/0.55  % (27145)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (27157)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.56  % (27158)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.71/0.61  % (27161)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.77/0.72  % (27167)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.77/0.72  % (27168)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.09/0.81  % (27136)Time limit reached!
% 3.09/0.81  % (27136)------------------------------
% 3.09/0.81  % (27136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.81  % (27136)Termination reason: Time limit
% 3.09/0.81  % (27136)Termination phase: Saturation
% 3.09/0.81  
% 3.09/0.81  % (27136)Memory used [KB]: 8699
% 3.09/0.81  % (27136)Time elapsed: 0.400 s
% 3.09/0.81  % (27136)------------------------------
% 3.09/0.81  % (27136)------------------------------
% 3.75/0.85  % (27147)Refutation found. Thanks to Tanya!
% 3.75/0.85  % SZS status Theorem for theBenchmark
% 3.75/0.85  % SZS output start Proof for theBenchmark
% 3.75/0.85  fof(f4292,plain,(
% 3.75/0.85    $false),
% 3.75/0.85    inference(avatar_sat_refutation,[],[f45,f50,f59,f560,f838,f1362,f1369,f1371,f1596,f1749,f2411,f2830,f2938,f2967,f3119,f3120,f3379,f3751,f3781,f3794,f3872,f3877,f4197,f4291])).
% 3.75/0.85  fof(f4291,plain,(
% 3.75/0.85    ~spl6_64 | ~spl6_74 | spl6_103),
% 3.75/0.85    inference(avatar_contradiction_clause,[],[f4284])).
% 3.75/0.85  fof(f4284,plain,(
% 3.75/0.85    $false | (~spl6_64 | ~spl6_74 | spl6_103)),
% 3.75/0.85    inference(resolution,[],[f3903,f3058])).
% 3.75/0.85  fof(f3058,plain,(
% 3.75/0.85    ~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1)) | spl6_103),
% 3.75/0.85    inference(avatar_component_clause,[],[f3056])).
% 3.75/0.85  fof(f3056,plain,(
% 3.75/0.85    spl6_103 <=> r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).
% 3.75/0.85  fof(f3903,plain,(
% 3.75/0.85    ( ! [X2,X3] : (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(k1_xboole_0,X3))) ) | (~spl6_64 | ~spl6_74)),
% 3.75/0.85    inference(backward_demodulation,[],[f1734,f1099])).
% 3.75/0.85  fof(f1099,plain,(
% 3.75/0.85    k1_xboole_0 = sK0 | ~spl6_64),
% 3.75/0.85    inference(avatar_component_clause,[],[f1098])).
% 3.75/0.85  fof(f1098,plain,(
% 3.75/0.85    spl6_64 <=> k1_xboole_0 = sK0),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 3.75/0.85  fof(f1734,plain,(
% 3.75/0.85    ( ! [X2,X3] : (r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(k1_xboole_0,X3))) ) | ~spl6_74),
% 3.75/0.85    inference(resolution,[],[f1445,f39])).
% 3.75/0.85  fof(f39,plain,(
% 3.75/0.85    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.75/0.85    inference(cnf_transformation,[],[f23])).
% 3.75/0.85  fof(f23,plain,(
% 3.75/0.85    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 3.75/0.85    inference(ennf_transformation,[],[f9])).
% 3.75/0.85  fof(f9,axiom,(
% 3.75/0.85    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 3.75/0.85  fof(f1445,plain,(
% 3.75/0.85    r1_xboole_0(sK0,k1_xboole_0) | ~spl6_74),
% 3.75/0.85    inference(avatar_component_clause,[],[f1443])).
% 3.75/0.85  fof(f1443,plain,(
% 3.75/0.85    spl6_74 <=> r1_xboole_0(sK0,k1_xboole_0)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 3.75/0.85  fof(f4197,plain,(
% 3.75/0.85    ~spl6_103 | spl6_43 | ~spl6_64),
% 3.75/0.85    inference(avatar_split_clause,[],[f4196,f1098,f658,f3056])).
% 3.75/0.85  fof(f658,plain,(
% 3.75/0.85    spl6_43 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 3.75/0.85  fof(f4196,plain,(
% 3.75/0.85    ~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1)) | (spl6_43 | ~spl6_64)),
% 3.75/0.85    inference(forward_demodulation,[],[f660,f1099])).
% 3.75/0.85  fof(f660,plain,(
% 3.75/0.85    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | spl6_43),
% 3.75/0.85    inference(avatar_component_clause,[],[f658])).
% 3.75/0.85  fof(f3877,plain,(
% 3.75/0.85    spl6_11 | ~spl6_5),
% 3.75/0.85    inference(avatar_split_clause,[],[f3852,f71,f203])).
% 3.75/0.85  fof(f203,plain,(
% 3.75/0.85    spl6_11 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 3.75/0.85  fof(f71,plain,(
% 3.75/0.85    spl6_5 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.75/0.85  fof(f3852,plain,(
% 3.75/0.85    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | ~spl6_5),
% 3.75/0.85    inference(superposition,[],[f93,f73])).
% 3.75/0.85  fof(f73,plain,(
% 3.75/0.85    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_5),
% 3.75/0.85    inference(avatar_component_clause,[],[f71])).
% 3.75/0.85  fof(f93,plain,(
% 3.75/0.85    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 3.75/0.85    inference(superposition,[],[f67,f30])).
% 3.75/0.85  fof(f30,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.75/0.85    inference(cnf_transformation,[],[f1])).
% 3.75/0.85  fof(f1,axiom,(
% 3.75/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.75/0.85  fof(f67,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 3.75/0.85    inference(resolution,[],[f33,f29])).
% 3.75/0.85  fof(f29,plain,(
% 3.75/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.75/0.85    inference(cnf_transformation,[],[f6])).
% 3.75/0.85  fof(f6,axiom,(
% 3.75/0.85    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.75/0.85  fof(f33,plain,(
% 3.75/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.75/0.85    inference(cnf_transformation,[],[f20])).
% 3.75/0.85  fof(f20,plain,(
% 3.75/0.85    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.75/0.85    inference(ennf_transformation,[],[f7])).
% 3.75/0.85  fof(f7,axiom,(
% 3.75/0.85    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.75/0.85  fof(f3872,plain,(
% 3.75/0.85    ~spl6_7 | spl6_8 | ~spl6_5),
% 3.75/0.85    inference(avatar_split_clause,[],[f3836,f71,f189,f185])).
% 3.75/0.85  fof(f185,plain,(
% 3.75/0.85    spl6_7 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 3.75/0.85  fof(f189,plain,(
% 3.75/0.85    spl6_8 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 3.75/0.85  fof(f3836,plain,(
% 3.75/0.85    ( ! [X8] : (~r2_hidden(X8,k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ) | ~spl6_5),
% 3.75/0.85    inference(superposition,[],[f31,f73])).
% 3.75/0.85  fof(f31,plain,(
% 3.75/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.75/0.85    inference(cnf_transformation,[],[f19])).
% 3.75/0.85  fof(f19,plain,(
% 3.75/0.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.75/0.85    inference(ennf_transformation,[],[f13])).
% 3.75/0.85  fof(f13,plain,(
% 3.75/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.75/0.85    inference(rectify,[],[f5])).
% 3.75/0.85  fof(f5,axiom,(
% 3.75/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.75/0.85  fof(f3794,plain,(
% 3.75/0.85    spl6_5 | ~spl6_2),
% 3.75/0.85    inference(avatar_split_clause,[],[f3793,f47,f71])).
% 3.75/0.85  fof(f47,plain,(
% 3.75/0.85    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.75/0.85  fof(f3793,plain,(
% 3.75/0.85    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_2),
% 3.75/0.85    inference(resolution,[],[f49,f33])).
% 3.75/0.85  fof(f49,plain,(
% 3.75/0.85    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_2),
% 3.75/0.85    inference(avatar_component_clause,[],[f47])).
% 3.75/0.85  fof(f3781,plain,(
% 3.75/0.85    spl6_4 | ~spl6_60),
% 3.75/0.85    inference(avatar_split_clause,[],[f1079,f973,f56])).
% 3.75/0.85  fof(f56,plain,(
% 3.75/0.85    spl6_4 <=> r1_tarski(sK0,sK2)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.75/0.85  fof(f973,plain,(
% 3.75/0.85    spl6_60 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 3.75/0.85  fof(f1079,plain,(
% 3.75/0.85    r1_tarski(sK0,sK2) | ~spl6_60),
% 3.75/0.85    inference(superposition,[],[f60,f975])).
% 3.75/0.85  fof(f975,plain,(
% 3.75/0.85    sK0 = k3_xboole_0(sK0,sK2) | ~spl6_60),
% 3.75/0.85    inference(avatar_component_clause,[],[f973])).
% 3.75/0.85  fof(f60,plain,(
% 3.75/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.75/0.85    inference(superposition,[],[f29,f30])).
% 3.75/0.85  fof(f3751,plain,(
% 3.75/0.85    ~spl6_32 | spl6_110),
% 3.75/0.85    inference(avatar_contradiction_clause,[],[f3744])).
% 3.75/0.85  fof(f3744,plain,(
% 3.75/0.85    $false | (~spl6_32 | spl6_110)),
% 3.75/0.85    inference(resolution,[],[f2949,f3254])).
% 3.75/0.85  fof(f3254,plain,(
% 3.75/0.85    ~r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) | spl6_110),
% 3.75/0.85    inference(avatar_component_clause,[],[f3252])).
% 3.75/0.85  fof(f3252,plain,(
% 3.75/0.85    spl6_110 <=> r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 3.75/0.85  fof(f2949,plain,(
% 3.75/0.85    ( ! [X2,X3] : (r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK2,X3))) ) | ~spl6_32),
% 3.75/0.85    inference(resolution,[],[f481,f39])).
% 3.75/0.85  fof(f481,plain,(
% 3.75/0.85    r1_xboole_0(sK0,sK2) | ~spl6_32),
% 3.75/0.85    inference(avatar_component_clause,[],[f480])).
% 3.75/0.85  fof(f480,plain,(
% 3.75/0.85    spl6_32 <=> r1_xboole_0(sK0,sK2)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 3.75/0.85  fof(f3379,plain,(
% 3.75/0.85    ~spl6_110 | spl6_7 | ~spl6_63),
% 3.75/0.85    inference(avatar_split_clause,[],[f3378,f1067,f185,f3252])).
% 3.75/0.85  fof(f1067,plain,(
% 3.75/0.85    spl6_63 <=> k1_xboole_0 = sK1),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 3.75/0.85  fof(f3378,plain,(
% 3.75/0.85    ~r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) | (spl6_7 | ~spl6_63)),
% 3.75/0.85    inference(forward_demodulation,[],[f187,f1069])).
% 3.75/0.85  fof(f1069,plain,(
% 3.75/0.85    k1_xboole_0 = sK1 | ~spl6_63),
% 3.75/0.85    inference(avatar_component_clause,[],[f1067])).
% 3.75/0.85  fof(f187,plain,(
% 3.75/0.85    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | spl6_7),
% 3.75/0.85    inference(avatar_component_clause,[],[f185])).
% 3.75/0.85  fof(f3120,plain,(
% 3.75/0.85    spl6_15 | spl6_16 | spl6_30 | ~spl6_5),
% 3.75/0.85    inference(avatar_split_clause,[],[f3083,f71,f450,f349,f345])).
% 3.75/0.85  fof(f345,plain,(
% 3.75/0.85    spl6_15 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 3.75/0.85  fof(f349,plain,(
% 3.75/0.85    spl6_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 3.75/0.85  fof(f450,plain,(
% 3.75/0.85    spl6_30 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X1)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 3.75/0.85  fof(f3083,plain,(
% 3.75/0.85    ( ! [X4,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK1,sK3) = X5) ) | ~spl6_5),
% 3.75/0.85    inference(superposition,[],[f136,f73])).
% 3.75/0.85  fof(f136,plain,(
% 3.75/0.85    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) = X5) )),
% 3.75/0.85    inference(superposition,[],[f38,f36])).
% 3.75/0.85  fof(f36,plain,(
% 3.75/0.85    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.75/0.85    inference(cnf_transformation,[],[f8])).
% 3.75/0.85  fof(f8,axiom,(
% 3.75/0.85    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 3.75/0.85  fof(f38,plain,(
% 3.75/0.85    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 3.75/0.85    inference(cnf_transformation,[],[f22])).
% 3.75/0.85  fof(f22,plain,(
% 3.75/0.85    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 3.75/0.85    inference(flattening,[],[f21])).
% 3.75/0.85  fof(f21,plain,(
% 3.75/0.85    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 3.75/0.85    inference(ennf_transformation,[],[f10])).
% 3.75/0.85  fof(f10,axiom,(
% 3.75/0.85    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 3.75/0.85  fof(f3119,plain,(
% 3.75/0.85    spl6_15 | spl6_16 | spl6_17 | ~spl6_5),
% 3.75/0.85    inference(avatar_split_clause,[],[f3081,f71,f353,f349,f345])).
% 3.75/0.85  fof(f353,plain,(
% 3.75/0.85    spl6_17 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK0,sK2) = X0)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 3.75/0.85  fof(f3081,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK0,sK2) = X0) ) | ~spl6_5),
% 3.75/0.85    inference(superposition,[],[f112,f73])).
% 3.75/0.85  fof(f112,plain,(
% 3.75/0.85    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X0,X1) = X4) )),
% 3.75/0.85    inference(superposition,[],[f37,f36])).
% 3.75/0.85  fof(f37,plain,(
% 3.75/0.85    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X0 = X2) )),
% 3.75/0.85    inference(cnf_transformation,[],[f22])).
% 3.75/0.85  fof(f2967,plain,(
% 3.75/0.85    spl6_63 | spl6_64 | ~spl6_5 | ~spl6_16),
% 3.75/0.85    inference(avatar_split_clause,[],[f2966,f349,f71,f1098,f1067])).
% 3.75/0.85  fof(f2966,plain,(
% 3.75/0.85    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl6_5 | ~spl6_16)),
% 3.75/0.85    inference(equality_resolution,[],[f2959])).
% 3.75/0.85  fof(f2959,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | (~spl6_5 | ~spl6_16)),
% 3.75/0.85    inference(duplicate_literal_removal,[],[f2958])).
% 3.75/0.85  fof(f2958,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | (~spl6_5 | ~spl6_16)),
% 3.75/0.85    inference(forward_demodulation,[],[f314,f351])).
% 3.75/0.85  fof(f351,plain,(
% 3.75/0.85    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl6_16),
% 3.75/0.85    inference(avatar_component_clause,[],[f349])).
% 3.75/0.85  fof(f314,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k3_xboole_0(sK0,sK2) = X0) ) | ~spl6_5),
% 3.75/0.85    inference(superposition,[],[f113,f73])).
% 3.75/0.85  fof(f113,plain,(
% 3.75/0.85    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k3_xboole_0(X0,X1) = X4) )),
% 3.75/0.85    inference(superposition,[],[f37,f36])).
% 3.75/0.85  fof(f2938,plain,(
% 3.75/0.85    spl6_32 | ~spl6_16),
% 3.75/0.85    inference(avatar_split_clause,[],[f2935,f349,f480])).
% 3.75/0.85  fof(f2935,plain,(
% 3.75/0.85    r1_xboole_0(sK0,sK2) | ~spl6_16),
% 3.75/0.85    inference(trivial_inequality_removal,[],[f2901])).
% 3.75/0.85  fof(f2901,plain,(
% 3.75/0.85    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl6_16),
% 3.75/0.85    inference(superposition,[],[f34,f351])).
% 3.75/0.85  fof(f34,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 3.75/0.85    inference(cnf_transformation,[],[f3])).
% 3.75/0.85  fof(f3,axiom,(
% 3.75/0.85    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.75/0.85  fof(f2830,plain,(
% 3.75/0.85    spl6_3 | ~spl6_79),
% 3.75/0.85    inference(avatar_split_clause,[],[f2785,f1523,f52])).
% 3.75/0.85  fof(f52,plain,(
% 3.75/0.85    spl6_3 <=> r1_tarski(sK1,sK3)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.75/0.85  fof(f1523,plain,(
% 3.75/0.85    spl6_79 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 3.75/0.85  fof(f2785,plain,(
% 3.75/0.85    r1_tarski(sK1,sK3) | ~spl6_79),
% 3.75/0.85    inference(superposition,[],[f60,f1525])).
% 3.75/0.85  fof(f1525,plain,(
% 3.75/0.85    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_79),
% 3.75/0.85    inference(avatar_component_clause,[],[f1523])).
% 3.75/0.85  fof(f2411,plain,(
% 3.75/0.85    spl6_60 | ~spl6_17),
% 3.75/0.85    inference(avatar_split_clause,[],[f2410,f353,f973])).
% 3.75/0.85  fof(f2410,plain,(
% 3.75/0.85    sK0 = k3_xboole_0(sK0,sK2) | ~spl6_17),
% 3.75/0.85    inference(equality_resolution,[],[f354])).
% 3.75/0.85  fof(f354,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK0,sK2) = X0) ) | ~spl6_17),
% 3.75/0.85    inference(avatar_component_clause,[],[f353])).
% 3.75/0.85  fof(f1749,plain,(
% 3.75/0.85    spl6_79 | ~spl6_30),
% 3.75/0.85    inference(avatar_split_clause,[],[f1748,f450,f1523])).
% 3.75/0.85  fof(f1748,plain,(
% 3.75/0.85    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_30),
% 3.75/0.85    inference(equality_resolution,[],[f451])).
% 3.75/0.85  fof(f451,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X1) ) | ~spl6_30),
% 3.75/0.85    inference(avatar_component_clause,[],[f450])).
% 3.75/0.85  fof(f1596,plain,(
% 3.75/0.85    spl6_74 | ~spl6_16),
% 3.75/0.85    inference(avatar_split_clause,[],[f1585,f349,f1443])).
% 3.75/0.85  fof(f1585,plain,(
% 3.75/0.85    r1_xboole_0(sK0,k1_xboole_0) | ~spl6_16),
% 3.75/0.85    inference(trivial_inequality_removal,[],[f1580])).
% 3.75/0.85  fof(f1580,plain,(
% 3.75/0.85    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k1_xboole_0) | ~spl6_16),
% 3.75/0.85    inference(superposition,[],[f105,f351])).
% 3.75/0.85  fof(f105,plain,(
% 3.75/0.85    ( ! [X26,X27] : (k1_xboole_0 != k3_xboole_0(X26,X27) | r1_xboole_0(X26,k3_xboole_0(X26,X27))) )),
% 3.75/0.85    inference(superposition,[],[f75,f67])).
% 3.75/0.85  fof(f75,plain,(
% 3.75/0.85    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 3.75/0.85    inference(superposition,[],[f34,f30])).
% 3.75/0.85  fof(f1371,plain,(
% 3.75/0.85    spl6_1 | ~spl6_13),
% 3.75/0.85    inference(avatar_split_clause,[],[f1370,f216,f42])).
% 3.75/0.85  fof(f42,plain,(
% 3.75/0.85    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.75/0.85  fof(f216,plain,(
% 3.75/0.85    spl6_13 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 3.75/0.85  fof(f1370,plain,(
% 3.75/0.85    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_13),
% 3.75/0.85    inference(resolution,[],[f218,f27])).
% 3.75/0.85  fof(f27,plain,(
% 3.75/0.85    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 3.75/0.85    inference(cnf_transformation,[],[f17])).
% 3.75/0.85  fof(f17,plain,(
% 3.75/0.85    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.75/0.85    inference(ennf_transformation,[],[f4])).
% 3.75/0.85  fof(f4,axiom,(
% 3.75/0.85    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.75/0.85  fof(f218,plain,(
% 3.75/0.85    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl6_13),
% 3.75/0.85    inference(avatar_component_clause,[],[f216])).
% 3.75/0.85  fof(f1369,plain,(
% 3.75/0.85    spl6_13 | ~spl6_8),
% 3.75/0.85    inference(avatar_split_clause,[],[f1364,f189,f216])).
% 3.75/0.85  fof(f1364,plain,(
% 3.75/0.85    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl6_8),
% 3.75/0.85    inference(resolution,[],[f190,f28])).
% 3.75/0.85  fof(f28,plain,(
% 3.75/0.85    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 3.75/0.85    inference(cnf_transformation,[],[f18])).
% 3.75/0.85  fof(f18,plain,(
% 3.75/0.85    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 3.75/0.85    inference(ennf_transformation,[],[f14])).
% 3.75/0.85  fof(f14,plain,(
% 3.75/0.85    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 3.75/0.85    inference(unused_predicate_definition_removal,[],[f2])).
% 3.75/0.85  fof(f2,axiom,(
% 3.75/0.85    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.75/0.85  fof(f190,plain,(
% 3.75/0.85    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl6_8),
% 3.75/0.85    inference(avatar_component_clause,[],[f189])).
% 3.75/0.85  fof(f1362,plain,(
% 3.75/0.85    spl6_7 | ~spl6_19),
% 3.75/0.85    inference(avatar_contradiction_clause,[],[f1355])).
% 3.75/0.85  fof(f1355,plain,(
% 3.75/0.85    $false | (spl6_7 | ~spl6_19)),
% 3.75/0.85    inference(resolution,[],[f572,f187])).
% 3.75/0.85  fof(f572,plain,(
% 3.75/0.85    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) ) | ~spl6_19),
% 3.75/0.85    inference(resolution,[],[f384,f40])).
% 3.75/0.85  fof(f40,plain,(
% 3.75/0.85    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.75/0.85    inference(cnf_transformation,[],[f23])).
% 3.75/0.85  fof(f384,plain,(
% 3.75/0.85    r1_xboole_0(sK1,sK3) | ~spl6_19),
% 3.75/0.85    inference(avatar_component_clause,[],[f383])).
% 3.75/0.85  fof(f383,plain,(
% 3.75/0.85    spl6_19 <=> r1_xboole_0(sK1,sK3)),
% 3.75/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 3.75/0.85  fof(f838,plain,(
% 3.75/0.85    ~spl6_43 | spl6_8 | ~spl6_11),
% 3.75/0.85    inference(avatar_split_clause,[],[f810,f203,f189,f658])).
% 3.75/0.85  fof(f810,plain,(
% 3.75/0.85    ( ! [X23] : (~r2_hidden(X23,k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) ) | ~spl6_11),
% 3.75/0.85    inference(superposition,[],[f104,f205])).
% 3.75/0.85  fof(f205,plain,(
% 3.75/0.85    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | ~spl6_11),
% 3.75/0.85    inference(avatar_component_clause,[],[f203])).
% 3.75/0.85  fof(f104,plain,(
% 3.75/0.85    ( ! [X24,X23,X25] : (~r2_hidden(X25,k3_xboole_0(X23,X24)) | ~r1_xboole_0(X23,k3_xboole_0(X23,X24))) )),
% 3.75/0.85    inference(superposition,[],[f65,f67])).
% 3.75/0.85  fof(f65,plain,(
% 3.75/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 3.75/0.85    inference(superposition,[],[f31,f30])).
% 3.75/0.85  fof(f560,plain,(
% 3.75/0.85    spl6_19 | ~spl6_15),
% 3.75/0.85    inference(avatar_split_clause,[],[f556,f345,f383])).
% 3.75/0.85  fof(f556,plain,(
% 3.75/0.85    r1_xboole_0(sK1,sK3) | ~spl6_15),
% 3.75/0.85    inference(trivial_inequality_removal,[],[f539])).
% 3.75/0.85  fof(f539,plain,(
% 3.75/0.85    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK3) | ~spl6_15),
% 3.75/0.85    inference(superposition,[],[f34,f347])).
% 3.75/0.85  fof(f347,plain,(
% 3.75/0.85    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl6_15),
% 3.75/0.85    inference(avatar_component_clause,[],[f345])).
% 3.75/0.85  fof(f59,plain,(
% 3.75/0.85    ~spl6_3 | ~spl6_4),
% 3.75/0.85    inference(avatar_split_clause,[],[f24,f56,f52])).
% 3.75/0.85  fof(f24,plain,(
% 3.75/0.85    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 3.75/0.85    inference(cnf_transformation,[],[f16])).
% 3.75/0.85  fof(f16,plain,(
% 3.75/0.85    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.75/0.85    inference(flattening,[],[f15])).
% 3.75/0.85  fof(f15,plain,(
% 3.75/0.85    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.75/0.85    inference(ennf_transformation,[],[f12])).
% 3.75/0.85  fof(f12,negated_conjecture,(
% 3.75/0.85    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.75/0.85    inference(negated_conjecture,[],[f11])).
% 3.75/0.85  fof(f11,conjecture,(
% 3.75/0.85    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.75/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 3.75/0.85  fof(f50,plain,(
% 3.75/0.85    spl6_2),
% 3.75/0.85    inference(avatar_split_clause,[],[f25,f47])).
% 3.75/0.85  fof(f25,plain,(
% 3.75/0.85    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.75/0.85    inference(cnf_transformation,[],[f16])).
% 3.75/0.85  fof(f45,plain,(
% 3.75/0.85    ~spl6_1),
% 3.75/0.85    inference(avatar_split_clause,[],[f26,f42])).
% 3.75/0.85  fof(f26,plain,(
% 3.75/0.85    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 3.75/0.85    inference(cnf_transformation,[],[f16])).
% 3.75/0.85  % SZS output end Proof for theBenchmark
% 3.75/0.85  % (27147)------------------------------
% 3.75/0.85  % (27147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.85  % (27147)Termination reason: Refutation
% 3.75/0.85  
% 3.75/0.85  % (27147)Memory used [KB]: 13432
% 3.75/0.85  % (27147)Time elapsed: 0.444 s
% 3.75/0.85  % (27147)------------------------------
% 3.75/0.85  % (27147)------------------------------
% 3.75/0.85  % (27130)Success in time 0.491 s
%------------------------------------------------------------------------------
