%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:35 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 194 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 ( 517 expanded)
%              Number of equality atoms :   47 (  95 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f403,f482,f802,f1147,f1152,f1451,f1631,f2063,f2093,f3133])).

fof(f3133,plain,
    ( ~ spl5_27
    | spl5_28 ),
    inference(avatar_contradiction_clause,[],[f3130])).

fof(f3130,plain,
    ( $false
    | ~ spl5_27
    | spl5_28 ),
    inference(subsumption_resolution,[],[f2066,f3120])).

fof(f3120,plain,
    ( ~ r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK2)
    | spl5_28 ),
    inference(resolution,[],[f2094,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2094,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(sK1,k1_setfam_1(sK2)))
        | ~ r2_hidden(X0,sK2) )
    | spl5_28 ),
    inference(resolution,[],[f2092,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f2092,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK3(sK1,k1_setfam_1(sK2)))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f2090])).

fof(f2090,plain,
    ( spl5_28
  <=> r1_tarski(k1_setfam_1(sK2),sK3(sK1,k1_setfam_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f2066,plain,
    ( r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK2)
    | ~ spl5_27 ),
    inference(resolution,[],[f2062,f83])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f31,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f2062,plain,
    ( r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f2060])).

fof(f2060,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f2093,plain,
    ( spl5_17
    | ~ spl5_28
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f1802,f799,f400,f2090,f795])).

fof(f795,plain,
    ( spl5_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f400,plain,
    ( spl5_13
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f799,plain,
    ( spl5_18
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1802,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK3(sK1,k1_setfam_1(sK2)))
    | k1_xboole_0 = sK1
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(resolution,[],[f1777,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f1777,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f640,f801])).

fof(f801,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f799])).

fof(f640,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f32,f402])).

fof(f402,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f400])).

fof(f32,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f2063,plain,
    ( spl5_17
    | spl5_27
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f1801,f799,f400,f2060,f795])).

fof(f1801,plain,
    ( r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK1)
    | k1_xboole_0 = sK1
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(resolution,[],[f1777,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1631,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f1619])).

fof(f1619,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f1142,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1142,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f1140])).

fof(f1140,plain,
    ( spl5_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1451,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f1446])).

fof(f1446,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f1415,f61])).

fof(f1415,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK1),k8_setfam_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f32,f145])).

fof(f145,plain,
    ( sK1 = sK2
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1152,plain,
    ( ~ spl5_13
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f1148])).

fof(f1148,plain,
    ( $false
    | ~ spl5_13
    | spl5_21 ),
    inference(subsumption_resolution,[],[f638,f1146])).

fof(f1146,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f1144])).

fof(f1144,plain,
    ( spl5_21
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f638,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f165,f402])).

fof(f165,plain,(
    r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f1147,plain,
    ( ~ spl5_20
    | ~ spl5_21
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f876,f795,f400,f1144,f1140])).

fof(f876,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(superposition,[],[f835,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f835,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f640,f797])).

fof(f797,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f795])).

fof(f802,plain,
    ( spl5_17
    | spl5_18 ),
    inference(avatar_split_clause,[],[f763,f799,f795])).

fof(f763,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f103,f105])).

fof(f105,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f33,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f482,plain,
    ( spl5_2
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | spl5_2
    | ~ spl5_12 ),
    inference(resolution,[],[f422,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f422,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl5_2
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f149,f398])).

fof(f398,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f149,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f403,plain,
    ( spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f363,f400,f396])).

fof(f363,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f69,f71])).

fof(f71,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f30,f42])).

fof(f69,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f30,f45])).

fof(f150,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f147,f143])).

fof(f67,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:13:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (5850)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (5852)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (5871)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (5853)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (5862)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (5870)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (5863)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (5854)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (5865)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (5868)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (5861)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (5855)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (5851)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (5858)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (5858)Refutation not found, incomplete strategy% (5858)------------------------------
% 0.21/0.52  % (5858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5858)Memory used [KB]: 10490
% 0.21/0.52  % (5858)Time elapsed: 0.107 s
% 0.21/0.52  % (5858)------------------------------
% 0.21/0.52  % (5858)------------------------------
% 0.21/0.52  % (5860)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (5860)Refutation not found, incomplete strategy% (5860)------------------------------
% 0.21/0.53  % (5860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5860)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5860)Memory used [KB]: 6140
% 0.21/0.53  % (5860)Time elapsed: 0.079 s
% 0.21/0.53  % (5860)------------------------------
% 0.21/0.53  % (5860)------------------------------
% 0.21/0.54  % (5848)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5847)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (5847)Refutation not found, incomplete strategy% (5847)------------------------------
% 0.21/0.54  % (5847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5847)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5847)Memory used [KB]: 10490
% 0.21/0.54  % (5847)Time elapsed: 0.125 s
% 0.21/0.54  % (5847)------------------------------
% 0.21/0.54  % (5847)------------------------------
% 0.21/0.54  % (5849)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (5859)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (5856)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (5866)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (5872)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (5857)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (5853)Refutation not found, incomplete strategy% (5853)------------------------------
% 0.21/0.55  % (5853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5853)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5853)Memory used [KB]: 10874
% 0.21/0.55  % (5853)Time elapsed: 0.114 s
% 0.21/0.55  % (5853)------------------------------
% 0.21/0.55  % (5853)------------------------------
% 0.21/0.56  % (5869)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (5873)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (5864)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.96/0.62  % (5868)Refutation found. Thanks to Tanya!
% 1.96/0.62  % SZS status Theorem for theBenchmark
% 1.96/0.62  % SZS output start Proof for theBenchmark
% 1.96/0.62  fof(f3134,plain,(
% 1.96/0.62    $false),
% 1.96/0.62    inference(avatar_sat_refutation,[],[f150,f403,f482,f802,f1147,f1152,f1451,f1631,f2063,f2093,f3133])).
% 1.96/0.62  fof(f3133,plain,(
% 1.96/0.62    ~spl5_27 | spl5_28),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f3130])).
% 1.96/0.62  fof(f3130,plain,(
% 1.96/0.62    $false | (~spl5_27 | spl5_28)),
% 1.96/0.62    inference(subsumption_resolution,[],[f2066,f3120])).
% 1.96/0.62  fof(f3120,plain,(
% 1.96/0.62    ~r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK2) | spl5_28),
% 1.96/0.62    inference(resolution,[],[f2094,f61])).
% 1.96/0.62  fof(f61,plain,(
% 1.96/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.96/0.62    inference(equality_resolution,[],[f48])).
% 1.96/0.62  fof(f48,plain,(
% 1.96/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.96/0.62    inference(cnf_transformation,[],[f1])).
% 1.96/0.62  fof(f1,axiom,(
% 1.96/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.96/0.62  fof(f2094,plain,(
% 1.96/0.62    ( ! [X0] : (~r1_tarski(X0,sK3(sK1,k1_setfam_1(sK2))) | ~r2_hidden(X0,sK2)) ) | spl5_28),
% 1.96/0.62    inference(resolution,[],[f2092,f57])).
% 1.96/0.62  fof(f57,plain,(
% 1.96/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(X1),X2)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f27])).
% 1.96/0.62  fof(f27,plain,(
% 1.96/0.62    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.96/0.62    inference(flattening,[],[f26])).
% 1.96/0.62  fof(f26,plain,(
% 1.96/0.62    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.96/0.62    inference(ennf_transformation,[],[f14])).
% 1.96/0.62  fof(f14,axiom,(
% 1.96/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.96/0.62  fof(f2092,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),sK3(sK1,k1_setfam_1(sK2))) | spl5_28),
% 1.96/0.62    inference(avatar_component_clause,[],[f2090])).
% 1.96/0.62  fof(f2090,plain,(
% 1.96/0.62    spl5_28 <=> r1_tarski(k1_setfam_1(sK2),sK3(sK1,k1_setfam_1(sK2)))),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.96/0.62  fof(f2066,plain,(
% 1.96/0.62    r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK2) | ~spl5_27),
% 1.96/0.62    inference(resolution,[],[f2062,f83])).
% 1.96/0.62  fof(f83,plain,(
% 1.96/0.62    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 1.96/0.62    inference(resolution,[],[f65,f41])).
% 1.96/0.62  fof(f41,plain,(
% 1.96/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f20])).
% 1.96/0.62  fof(f20,plain,(
% 1.96/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.96/0.62    inference(ennf_transformation,[],[f6])).
% 1.96/0.62  fof(f6,axiom,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.96/0.62  fof(f65,plain,(
% 1.96/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 1.96/0.62    inference(resolution,[],[f31,f55])).
% 1.96/0.62  fof(f55,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f11])).
% 1.96/0.62  fof(f11,axiom,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.96/0.62  fof(f31,plain,(
% 1.96/0.62    r1_tarski(sK1,sK2)),
% 1.96/0.62    inference(cnf_transformation,[],[f18])).
% 1.96/0.62  fof(f18,plain,(
% 1.96/0.62    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.96/0.62    inference(flattening,[],[f17])).
% 1.96/0.62  fof(f17,plain,(
% 1.96/0.62    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.96/0.62    inference(ennf_transformation,[],[f16])).
% 1.96/0.62  fof(f16,negated_conjecture,(
% 1.96/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.96/0.62    inference(negated_conjecture,[],[f15])).
% 1.96/0.62  fof(f15,conjecture,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.96/0.62  fof(f2062,plain,(
% 1.96/0.62    r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK1) | ~spl5_27),
% 1.96/0.62    inference(avatar_component_clause,[],[f2060])).
% 1.96/0.62  fof(f2060,plain,(
% 1.96/0.62    spl5_27 <=> r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK1)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.96/0.62  fof(f2093,plain,(
% 1.96/0.62    spl5_17 | ~spl5_28 | ~spl5_13 | ~spl5_18),
% 1.96/0.62    inference(avatar_split_clause,[],[f1802,f799,f400,f2090,f795])).
% 1.96/0.62  fof(f795,plain,(
% 1.96/0.62    spl5_17 <=> k1_xboole_0 = sK1),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.96/0.62  fof(f400,plain,(
% 1.96/0.62    spl5_13 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.96/0.62  fof(f799,plain,(
% 1.96/0.62    spl5_18 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.96/0.62  fof(f1802,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),sK3(sK1,k1_setfam_1(sK2))) | k1_xboole_0 = sK1 | (~spl5_13 | ~spl5_18)),
% 1.96/0.62    inference(resolution,[],[f1777,f47])).
% 1.96/0.62  fof(f47,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~r1_tarski(X1,sK3(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f25])).
% 1.96/0.62  fof(f25,plain,(
% 1.96/0.62    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.96/0.62    inference(flattening,[],[f24])).
% 1.96/0.62  fof(f24,plain,(
% 1.96/0.62    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.96/0.62    inference(ennf_transformation,[],[f13])).
% 1.96/0.62  fof(f13,axiom,(
% 1.96/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.96/0.62  fof(f1777,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl5_13 | ~spl5_18)),
% 1.96/0.62    inference(backward_demodulation,[],[f640,f801])).
% 1.96/0.62  fof(f801,plain,(
% 1.96/0.62    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl5_18),
% 1.96/0.62    inference(avatar_component_clause,[],[f799])).
% 1.96/0.62  fof(f640,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | ~spl5_13),
% 1.96/0.62    inference(backward_demodulation,[],[f32,f402])).
% 1.96/0.62  fof(f402,plain,(
% 1.96/0.62    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl5_13),
% 1.96/0.62    inference(avatar_component_clause,[],[f400])).
% 1.96/0.62  fof(f32,plain,(
% 1.96/0.62    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.96/0.62    inference(cnf_transformation,[],[f18])).
% 1.96/0.62  fof(f2063,plain,(
% 1.96/0.62    spl5_17 | spl5_27 | ~spl5_13 | ~spl5_18),
% 1.96/0.62    inference(avatar_split_clause,[],[f1801,f799,f400,f2060,f795])).
% 1.96/0.62  fof(f1801,plain,(
% 1.96/0.62    r2_hidden(sK3(sK1,k1_setfam_1(sK2)),sK1) | k1_xboole_0 = sK1 | (~spl5_13 | ~spl5_18)),
% 1.96/0.62    inference(resolution,[],[f1777,f46])).
% 1.96/0.62  fof(f46,plain,(
% 1.96/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f25])).
% 1.96/0.62  fof(f1631,plain,(
% 1.96/0.62    spl5_20),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f1619])).
% 1.96/0.62  fof(f1619,plain,(
% 1.96/0.62    $false | spl5_20),
% 1.96/0.62    inference(resolution,[],[f1142,f36])).
% 1.96/0.62  fof(f36,plain,(
% 1.96/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f7])).
% 1.96/0.62  fof(f7,axiom,(
% 1.96/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.96/0.62  fof(f1142,plain,(
% 1.96/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl5_20),
% 1.96/0.62    inference(avatar_component_clause,[],[f1140])).
% 1.96/0.62  fof(f1140,plain,(
% 1.96/0.62    spl5_20 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.96/0.62  fof(f1451,plain,(
% 1.96/0.62    ~spl5_1),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f1446])).
% 1.96/0.62  fof(f1446,plain,(
% 1.96/0.62    $false | ~spl5_1),
% 1.96/0.62    inference(resolution,[],[f1415,f61])).
% 1.96/0.62  fof(f1415,plain,(
% 1.96/0.62    ~r1_tarski(k8_setfam_1(sK0,sK1),k8_setfam_1(sK0,sK1)) | ~spl5_1),
% 1.96/0.62    inference(forward_demodulation,[],[f32,f145])).
% 1.96/0.62  fof(f145,plain,(
% 1.96/0.62    sK1 = sK2 | ~spl5_1),
% 1.96/0.62    inference(avatar_component_clause,[],[f143])).
% 1.96/0.62  fof(f143,plain,(
% 1.96/0.62    spl5_1 <=> sK1 = sK2),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.96/0.62  fof(f1152,plain,(
% 1.96/0.62    ~spl5_13 | spl5_21),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f1148])).
% 1.96/0.62  fof(f1148,plain,(
% 1.96/0.62    $false | (~spl5_13 | spl5_21)),
% 1.96/0.62    inference(subsumption_resolution,[],[f638,f1146])).
% 1.96/0.62  fof(f1146,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl5_21),
% 1.96/0.62    inference(avatar_component_clause,[],[f1144])).
% 1.96/0.62  fof(f1144,plain,(
% 1.96/0.62    spl5_21 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.96/0.62  fof(f638,plain,(
% 1.96/0.62    r1_tarski(k1_setfam_1(sK2),sK0) | ~spl5_13),
% 1.96/0.62    inference(backward_demodulation,[],[f165,f402])).
% 1.96/0.62  fof(f165,plain,(
% 1.96/0.62    r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 1.96/0.62    inference(resolution,[],[f70,f56])).
% 1.96/0.62  fof(f56,plain,(
% 1.96/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f11])).
% 1.96/0.62  fof(f70,plain,(
% 1.96/0.62    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.96/0.62    inference(resolution,[],[f30,f43])).
% 1.96/0.62  fof(f43,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f22])).
% 1.96/0.62  fof(f22,plain,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.96/0.62    inference(ennf_transformation,[],[f9])).
% 1.96/0.62  fof(f9,axiom,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.96/0.62  fof(f30,plain,(
% 1.96/0.62    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.96/0.62    inference(cnf_transformation,[],[f18])).
% 1.96/0.62  fof(f1147,plain,(
% 1.96/0.62    ~spl5_20 | ~spl5_21 | ~spl5_13 | ~spl5_17),
% 1.96/0.62    inference(avatar_split_clause,[],[f876,f795,f400,f1144,f1140])).
% 1.96/0.62  fof(f876,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl5_13 | ~spl5_17)),
% 1.96/0.62    inference(superposition,[],[f835,f59])).
% 1.96/0.62  fof(f59,plain,(
% 1.96/0.62    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.96/0.62    inference(equality_resolution,[],[f44])).
% 1.96/0.62  fof(f44,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 1.96/0.62    inference(cnf_transformation,[],[f23])).
% 1.96/0.62  fof(f23,plain,(
% 1.96/0.62    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.96/0.62    inference(ennf_transformation,[],[f8])).
% 1.96/0.62  fof(f8,axiom,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.96/0.62  fof(f835,plain,(
% 1.96/0.62    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl5_13 | ~spl5_17)),
% 1.96/0.62    inference(backward_demodulation,[],[f640,f797])).
% 1.96/0.62  fof(f797,plain,(
% 1.96/0.62    k1_xboole_0 = sK1 | ~spl5_17),
% 1.96/0.62    inference(avatar_component_clause,[],[f795])).
% 1.96/0.62  fof(f802,plain,(
% 1.96/0.62    spl5_17 | spl5_18),
% 1.96/0.62    inference(avatar_split_clause,[],[f763,f799,f795])).
% 1.96/0.62  fof(f763,plain,(
% 1.96/0.62    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 1.96/0.62    inference(forward_demodulation,[],[f103,f105])).
% 1.96/0.62  fof(f105,plain,(
% 1.96/0.62    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.96/0.62    inference(resolution,[],[f33,f42])).
% 1.96/0.62  fof(f42,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f21])).
% 1.96/0.62  fof(f21,plain,(
% 1.96/0.62    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.96/0.62    inference(ennf_transformation,[],[f10])).
% 1.96/0.62  fof(f10,axiom,(
% 1.96/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.96/0.62  fof(f33,plain,(
% 1.96/0.62    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.96/0.62    inference(cnf_transformation,[],[f18])).
% 1.96/0.62  fof(f103,plain,(
% 1.96/0.62    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 1.96/0.62    inference(resolution,[],[f33,f45])).
% 1.96/0.62  fof(f45,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f23])).
% 1.96/0.62  fof(f482,plain,(
% 1.96/0.62    spl5_2 | ~spl5_12),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f476])).
% 1.96/0.62  fof(f476,plain,(
% 1.96/0.62    $false | (spl5_2 | ~spl5_12)),
% 1.96/0.62    inference(resolution,[],[f422,f35])).
% 1.96/0.62  fof(f35,plain,(
% 1.96/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f2])).
% 1.96/0.62  fof(f2,axiom,(
% 1.96/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.96/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.96/0.62  fof(f422,plain,(
% 1.96/0.62    ~r1_tarski(k1_xboole_0,sK1) | (spl5_2 | ~spl5_12)),
% 1.96/0.62    inference(backward_demodulation,[],[f149,f398])).
% 1.96/0.62  fof(f398,plain,(
% 1.96/0.62    k1_xboole_0 = sK2 | ~spl5_12),
% 1.96/0.62    inference(avatar_component_clause,[],[f396])).
% 1.96/0.62  fof(f396,plain,(
% 1.96/0.62    spl5_12 <=> k1_xboole_0 = sK2),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.96/0.62  fof(f149,plain,(
% 1.96/0.62    ~r1_tarski(sK2,sK1) | spl5_2),
% 1.96/0.62    inference(avatar_component_clause,[],[f147])).
% 1.96/0.62  fof(f147,plain,(
% 1.96/0.62    spl5_2 <=> r1_tarski(sK2,sK1)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.96/0.62  fof(f403,plain,(
% 1.96/0.62    spl5_12 | spl5_13),
% 1.96/0.62    inference(avatar_split_clause,[],[f363,f400,f396])).
% 1.96/0.62  fof(f363,plain,(
% 1.96/0.62    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.96/0.62    inference(forward_demodulation,[],[f69,f71])).
% 1.96/0.62  fof(f71,plain,(
% 1.96/0.62    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.96/0.62    inference(resolution,[],[f30,f42])).
% 1.96/0.62  fof(f69,plain,(
% 1.96/0.62    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.96/0.62    inference(resolution,[],[f30,f45])).
% 1.96/0.62  fof(f150,plain,(
% 1.96/0.62    spl5_1 | ~spl5_2),
% 1.96/0.62    inference(avatar_split_clause,[],[f67,f147,f143])).
% 1.96/0.62  fof(f67,plain,(
% 1.96/0.62    ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 1.96/0.62    inference(resolution,[],[f31,f50])).
% 1.96/0.62  fof(f50,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.96/0.62    inference(cnf_transformation,[],[f1])).
% 1.96/0.62  % SZS output end Proof for theBenchmark
% 1.96/0.62  % (5868)------------------------------
% 1.96/0.62  % (5868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.62  % (5868)Termination reason: Refutation
% 1.96/0.62  
% 1.96/0.62  % (5868)Memory used [KB]: 12153
% 1.96/0.62  % (5868)Time elapsed: 0.197 s
% 1.96/0.62  % (5868)------------------------------
% 1.96/0.62  % (5868)------------------------------
% 1.96/0.62  % (5846)Success in time 0.258 s
%------------------------------------------------------------------------------
