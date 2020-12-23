%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 233 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  252 ( 866 expanded)
%              Number of equality atoms :   18 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f48,f128,f130,f141,f143,f153,f159,f168,f221,f232])).

fof(f232,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f226,f220])).

fof(f220,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_10
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f226,plain,
    ( r1_tarski(sK1,sK1)
    | spl4_10 ),
    inference(resolution,[],[f223,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f223,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | spl4_10 ),
    inference(resolution,[],[f220,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f221,plain,
    ( ~ spl4_10
    | spl4_2
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f216,f156,f150,f40,f44,f218])).

fof(f44,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f40,plain,
    ( spl4_1
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f150,plain,
    ( spl4_7
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f156,plain,
    ( spl4_8
  <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f216,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f214,f158])).

fof(f158,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f214,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f188,f152])).

fof(f152,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f150])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,k4_xboole_0(X0,X1))
        | r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f175,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f175,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK1,X4)
        | r1_tarski(sK1,k4_xboole_0(X4,k4_xboole_0(sK0,sK2))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f38,f169])).

fof(f169,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f41,f78])).

fof(f78,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f41,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f168,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f164,f45])).

fof(f45,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f164,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1
    | ~ spl4_8 ),
    inference(superposition,[],[f81,f158])).

fof(f81,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))
    | spl4_1 ),
    inference(backward_demodulation,[],[f49,f78])).

fof(f49,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,k3_subset_1(sK0,sK2)))
    | spl4_1 ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f159,plain,
    ( ~ spl4_5
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f154,f138,f156,f134])).

fof(f134,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f138,plain,
    ( spl4_6
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f154,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f146,f144])).

fof(f144,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f140,f31])).

fof(f140,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f146,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f32,f78])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f153,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f148,f125,f150,f121])).

fof(f121,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f125,plain,
    ( spl4_4
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f148,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f145,f131])).

fof(f131,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f127,f31])).

fof(f127,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f145,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f32,f77])).

fof(f77,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f136,f27])).

fof(f136,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f141,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f132,f138,f134])).

fof(f132,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f30,f78])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f130,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f123,f26])).

fof(f123,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f128,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f30,f77])).

fof(f48,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f28,f44,f40])).

fof(f28,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f44,f40])).

fof(f29,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14487)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (14503)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (14487)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f47,f48,f128,f130,f141,f143,f153,f159,f168,f221,f232])).
% 0.20/0.49  fof(f232,plain,(
% 0.20/0.49    spl4_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f228])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    $false | spl4_10),
% 0.20/0.49    inference(resolution,[],[f226,f220])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    ~r1_tarski(sK1,sK1) | spl4_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f218])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    spl4_10 <=> r1_tarski(sK1,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    r1_tarski(sK1,sK1) | spl4_10),
% 0.20/0.49    inference(resolution,[],[f223,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK1,sK1),sK1) | spl4_10),
% 0.20/0.49    inference(resolution,[],[f220,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ~spl4_10 | spl4_2 | ~spl4_1 | ~spl4_7 | ~spl4_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f216,f156,f150,f40,f44,f218])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl4_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl4_1 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl4_7 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl4_8 <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    r1_tarski(sK1,sK2) | ~r1_tarski(sK1,sK1) | (~spl4_1 | ~spl4_7 | ~spl4_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f214,f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f156])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl4_1 | ~spl4_7)),
% 0.20/0.49    inference(superposition,[],[f188,f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f150])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(sK1,k4_xboole_0(X0,X1)) | r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f175,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ( ! [X4] : (~r1_tarski(sK1,X4) | r1_tarski(sK1,k4_xboole_0(X4,k4_xboole_0(sK0,sK2)))) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f38,f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_1),
% 0.20/0.49    inference(forward_demodulation,[],[f41,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(resolution,[],[f31,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f40])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl4_1 | ~spl4_2 | ~spl4_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    $false | (spl4_1 | ~spl4_2 | ~spl4_8)),
% 0.20/0.50    inference(resolution,[],[f164,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    r1_tarski(sK1,sK2) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f44])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK2) | (spl4_1 | ~spl4_8)),
% 0.20/0.50    inference(superposition,[],[f81,f158])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) ) | spl4_1),
% 0.20/0.50    inference(backward_demodulation,[],[f49,f78])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,k3_subset_1(sK0,sK2)))) ) | spl4_1),
% 0.20/0.50    inference(resolution,[],[f37,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f40])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    ~spl4_5 | spl4_8 | ~spl4_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f154,f138,f156,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    spl4_6 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.20/0.50    inference(forward_demodulation,[],[f146,f144])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_6),
% 0.20/0.50    inference(resolution,[],[f140,f31])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f138])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f32,f78])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ~spl4_3 | spl4_7 | ~spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f148,f125,f150,f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl4_4 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.20/0.50    inference(forward_demodulation,[],[f145,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_4),
% 0.20/0.50    inference(resolution,[],[f127,f31])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f125])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f32,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f31,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl4_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    $false | spl4_5),
% 0.20/0.50    inference(resolution,[],[f136,f27])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f134])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ~spl4_5 | spl4_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f132,f138,f134])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f30,f78])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    $false | spl4_3),
% 0.20/0.50    inference(resolution,[],[f123,f26])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f121])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~spl4_3 | spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f119,f125,f121])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f30,f77])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl4_1 | spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f44,f40])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ~spl4_1 | ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f44,f40])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (14487)------------------------------
% 0.20/0.50  % (14487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14487)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (14487)Memory used [KB]: 6268
% 0.20/0.50  % (14487)Time elapsed: 0.078 s
% 0.20/0.50  % (14487)------------------------------
% 0.20/0.50  % (14487)------------------------------
% 0.20/0.50  % (14474)Success in time 0.145 s
%------------------------------------------------------------------------------
