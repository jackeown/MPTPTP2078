%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 162 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  234 ( 395 expanded)
%              Number of equality atoms :   50 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f143,f148,f170,f234,f244,f266,f292,f347,f353,f360,f394])).

fof(f394,plain,
    ( ~ spl4_3
    | spl4_23
    | spl4_37 ),
    inference(avatar_split_clause,[],[f392,f357,f227,f62])).

fof(f62,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f227,plain,
    ( spl4_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f357,plain,
    ( spl4_37
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f392,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl4_37 ),
    inference(resolution,[],[f359,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f359,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f357])).

fof(f360,plain,
    ( ~ spl4_37
    | ~ spl4_26
    | spl4_36 ),
    inference(avatar_split_clause,[],[f355,f350,f241,f357])).

fof(f241,plain,
    ( spl4_26
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f350,plain,
    ( spl4_36
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f355,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl4_26
    | spl4_36 ),
    inference(forward_demodulation,[],[f352,f243])).

fof(f243,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f352,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f350])).

fof(f353,plain,
    ( ~ spl4_36
    | spl4_2
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f348,f231,f57,f350])).

fof(f57,plain,
    ( spl4_2
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f231,plain,
    ( spl4_24
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f348,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl4_2
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f59,f233])).

fof(f233,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f59,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f347,plain,
    ( spl4_23
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f344,f263,f227])).

fof(f263,plain,
    ( spl4_28
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f344,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_28 ),
    inference(resolution,[],[f265,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f265,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f263])).

fof(f292,plain,
    ( ~ spl4_16
    | spl4_2
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f291,f227,f57,f167])).

fof(f167,plain,
    ( spl4_16
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f291,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl4_2
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f290,f92])).

fof(f92,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f290,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl4_2
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f59,f229])).

fof(f229,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f266,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f247,f237,f62,f263])).

fof(f237,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f247,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f64,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f237])).

fof(f64,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f244,plain,
    ( spl4_25
    | spl4_26
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f235,f145,f67,f241,f237])).

fof(f67,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f145,plain,
    ( spl4_14
  <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f235,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f220,f147])).

fof(f147,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f220,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f37,f69])).

fof(f69,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f234,plain,
    ( spl4_23
    | spl4_24
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f225,f140,f52,f231,f227])).

fof(f52,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f140,plain,
    ( spl4_13
  <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f225,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f219,f142])).

fof(f142,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f219,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f170,plain,
    ( spl4_16
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f156,f67,f167])).

fof(f156,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f149,f69])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | r1_tarski(k8_setfam_1(X1,X0),X1) ) ),
    inference(resolution,[],[f35,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f72,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f148,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f136,f67,f145])).

fof(f136,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f143,plain,
    ( spl4_13
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f135,f52,f140])).

fof(f135,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f34,f54])).

fof(f70,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f65,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (19274)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.47  % (19265)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.47  % (19265)Refutation not found, incomplete strategy% (19265)------------------------------
% 0.20/0.47  % (19265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19265)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19265)Memory used [KB]: 10618
% 0.20/0.47  % (19265)Time elapsed: 0.005 s
% 0.20/0.47  % (19265)------------------------------
% 0.20/0.47  % (19265)------------------------------
% 0.20/0.47  % (19274)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f395,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f143,f148,f170,f234,f244,f266,f292,f347,f353,f360,f394])).
% 0.20/0.47  fof(f394,plain,(
% 0.20/0.47    ~spl4_3 | spl4_23 | spl4_37),
% 0.20/0.47    inference(avatar_split_clause,[],[f392,f357,f227,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl4_3 <=> r1_tarski(sK1,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    spl4_23 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    spl4_37 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.47  fof(f392,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl4_37),
% 0.20/0.47    inference(resolution,[],[f359,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl4_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f357])).
% 0.20/0.47  fof(f360,plain,(
% 0.20/0.47    ~spl4_37 | ~spl4_26 | spl4_36),
% 0.20/0.47    inference(avatar_split_clause,[],[f355,f350,f241,f357])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    spl4_26 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    spl4_36 <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.47  fof(f355,plain,(
% 0.20/0.47    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl4_26 | spl4_36)),
% 0.20/0.47    inference(forward_demodulation,[],[f352,f243])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f241])).
% 0.20/0.47  fof(f352,plain,(
% 0.20/0.47    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | spl4_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f350])).
% 0.20/0.47  fof(f353,plain,(
% 0.20/0.47    ~spl4_36 | spl4_2 | ~spl4_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f348,f231,f57,f350])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl4_2 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f231,plain,(
% 0.20/0.47    spl4_24 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.47  fof(f348,plain,(
% 0.20/0.47    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | (spl4_2 | ~spl4_24)),
% 0.20/0.47    inference(forward_demodulation,[],[f59,f233])).
% 0.20/0.47  fof(f233,plain,(
% 0.20/0.47    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f231])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f347,plain,(
% 0.20/0.47    spl4_23 | ~spl4_28),
% 0.20/0.47    inference(avatar_split_clause,[],[f344,f263,f227])).
% 0.20/0.47  fof(f263,plain,(
% 0.20/0.47    spl4_28 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.47  fof(f344,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl4_28),
% 0.20/0.47    inference(resolution,[],[f265,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(resolution,[],[f40,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    r1_tarski(sK1,k1_xboole_0) | ~spl4_28),
% 0.20/0.48    inference(avatar_component_clause,[],[f263])).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    ~spl4_16 | spl4_2 | ~spl4_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f291,f227,f57,f167])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    spl4_16 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | (spl4_2 | ~spl4_23)),
% 0.20/0.48    inference(forward_demodulation,[],[f290,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(resolution,[],[f46,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(equality_resolution,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.48  fof(f290,plain,(
% 0.20/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl4_2 | ~spl4_23)),
% 0.20/0.48    inference(forward_demodulation,[],[f59,f229])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl4_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f227])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    spl4_28 | ~spl4_3 | ~spl4_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f247,f237,f62,f263])).
% 0.20/0.48  fof(f237,plain,(
% 0.20/0.48    spl4_25 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    r1_tarski(sK1,k1_xboole_0) | (~spl4_3 | ~spl4_25)),
% 0.20/0.48    inference(backward_demodulation,[],[f64,f239])).
% 0.20/0.48  fof(f239,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl4_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f237])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    spl4_25 | spl4_26 | ~spl4_4 | ~spl4_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f235,f145,f67,f241,f237])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    spl4_14 <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | (~spl4_4 | ~spl4_14)),
% 0.20/0.48    inference(forward_demodulation,[],[f220,f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f145])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl4_4),
% 0.20/0.48    inference(resolution,[],[f37,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    spl4_23 | spl4_24 | ~spl4_1 | ~spl4_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f225,f140,f52,f231,f227])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl4_13 <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1 | (~spl4_1 | ~spl4_13)),
% 0.20/0.48    inference(forward_demodulation,[],[f219,f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f140])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f37,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    spl4_16 | ~spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f156,f67,f167])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_4),
% 0.20/0.48    inference(resolution,[],[f149,f69])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | r1_tarski(k8_setfam_1(X1,X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f35,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f72,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) )),
% 0.20/0.48    inference(resolution,[],[f33,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl4_14 | ~spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f136,f67,f145])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_4),
% 0.20/0.48    inference(resolution,[],[f34,f69])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl4_13 | ~spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f135,f52,f140])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f34,f54])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f67])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f12])).
% 0.20/0.48  fof(f12,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f62])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ~spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f57])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f52])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (19274)------------------------------
% 0.20/0.48  % (19274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19274)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (19274)Memory used [KB]: 6396
% 0.20/0.48  % (19274)Time elapsed: 0.015 s
% 0.20/0.48  % (19274)------------------------------
% 0.20/0.48  % (19274)------------------------------
% 0.20/0.48  % (19258)Success in time 0.119 s
%------------------------------------------------------------------------------
