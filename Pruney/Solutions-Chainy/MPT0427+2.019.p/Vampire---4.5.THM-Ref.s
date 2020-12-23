%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 524 expanded)
%              Number of leaves         :   17 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  312 (1826 expanded)
%              Number of equality atoms :   58 ( 225 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f703,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f345,f392,f469,f485,f646,f699])).

fof(f699,plain,
    ( ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f697,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f697,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f696,f496])).

fof(f496,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_11 ),
    inference(resolution,[],[f486,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f486,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f39,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f696,plain,
    ( ~ r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f521,f95])).

fof(f95,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f521,plain,
    ( ~ r1_tarski(sK0,k8_setfam_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f509,f496])).

fof(f509,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f41,f126])).

fof(f41,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f646,plain,
    ( spl4_6
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f643,f622])).

fof(f622,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f620,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK1
    | spl4_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f620,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl4_11 ),
    inference(resolution,[],[f574,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f574,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f475,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f475,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f295,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f295,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f40,f126])).

fof(f40,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f643,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | spl4_6
    | ~ spl4_11 ),
    inference(resolution,[],[f640,f593])).

fof(f593,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f573,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f573,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_11 ),
    inference(resolution,[],[f475,f60])).

fof(f60,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f640,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),sK1)
    | spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f638,f94])).

fof(f638,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ spl4_11 ),
    inference(resolution,[],[f575,f43])).

fof(f575,plain,
    ( ! [X1] :
        ( r1_xboole_0(sK1,X1)
        | r2_hidden(sK3(k1_xboole_0,X1),X1) )
    | ~ spl4_11 ),
    inference(resolution,[],[f475,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f485,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f482,f93,f89])).

fof(f89,plain,
    ( spl4_5
  <=> k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f482,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f469,plain,
    ( ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f390,f278])).

fof(f278,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f213,f273])).

fof(f273,plain,
    ( sK0 = k1_setfam_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f207,f223])).

fof(f223,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f194,f61])).

fof(f194,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f38,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f192,f40])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f189,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f189,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f160,f188])).

fof(f188,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f122,f117])).

fof(f117,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f122,plain,
    ( k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_10
  <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f160,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f41,f159])).

fof(f159,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f91,f86])).

fof(f86,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f38,f50])).

fof(f91,plain,
    ( k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f207,plain,
    ( k1_setfam_1(k1_xboole_0) = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f159,f193])).

fof(f213,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f189,f193])).

fof(f390,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f191,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f191,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f190,f39])).

fof(f190,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_10 ),
    inference(superposition,[],[f51,f188])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f392,plain,
    ( ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f390,f386])).

fof(f386,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f371,f188])).

fof(f371,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f356,f352])).

fof(f352,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(resolution,[],[f326,f61])).

fof(f326,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f38,f95])).

fof(f356,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f41,f95])).

fof(f345,plain,
    ( spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f342,f124,f120])).

fof(f342,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f39,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (12738)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (12738)Refutation not found, incomplete strategy% (12738)------------------------------
% 0.21/0.48  % (12738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12746)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (12743)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (12738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12738)Memory used [KB]: 10746
% 0.21/0.50  % (12738)Time elapsed: 0.057 s
% 0.21/0.50  % (12738)------------------------------
% 0.21/0.50  % (12738)------------------------------
% 0.21/0.50  % (12733)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (12743)Refutation not found, incomplete strategy% (12743)------------------------------
% 0.21/0.50  % (12743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12743)Memory used [KB]: 10490
% 0.21/0.50  % (12743)Time elapsed: 0.083 s
% 0.21/0.50  % (12743)------------------------------
% 0.21/0.50  % (12743)------------------------------
% 0.21/0.50  % (12742)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (12749)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (12734)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (12732)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (12752)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (12739)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (12733)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f703,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f345,f392,f469,f485,f646,f699])).
% 0.21/0.52  fof(f699,plain,(
% 0.21/0.52    ~spl4_6 | ~spl4_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f698])).
% 0.21/0.52  fof(f698,plain,(
% 0.21/0.52    $false | (~spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f697,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f697,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK0) | (~spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f696,f496])).
% 0.21/0.52  fof(f496,plain,(
% 0.21/0.52    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f486,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.52  fof(f486,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_11),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl4_11 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.52  fof(f696,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) | (~spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f521,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl4_6 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f521,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k8_setfam_1(sK0,sK1)) | ~spl4_11),
% 0.21/0.52    inference(backward_demodulation,[],[f509,f496])).
% 0.21/0.52  fof(f509,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) | ~spl4_11),
% 0.21/0.52    inference(forward_demodulation,[],[f41,f126])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f646,plain,(
% 0.21/0.52    spl4_6 | ~spl4_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f645])).
% 0.21/0.52  fof(f645,plain,(
% 0.21/0.52    $false | (spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f643,f622])).
% 0.21/0.52  fof(f622,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0) | (spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f620,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f620,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0) | k1_xboole_0 = sK1 | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f574,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.52  fof(f574,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(sK1,X0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f475,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(sK1,X0)) ) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f295,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    r1_tarski(sK1,k1_xboole_0) | ~spl4_11),
% 0.21/0.52    inference(backward_demodulation,[],[f40,f126])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f643,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0) | (spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(resolution,[],[f640,f593])).
% 0.21/0.52  fof(f593,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f573,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f573,plain,(
% 0.21/0.52    r1_xboole_0(sK1,k1_xboole_0) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f475,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(equality_resolution,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f640,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_xboole_0,sK1),sK1) | (spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f638,f94])).
% 0.21/0.52  fof(f638,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_xboole_0,sK1),sK1) | k1_xboole_0 = sK1 | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f575,f43])).
% 0.21/0.52  fof(f575,plain,(
% 0.21/0.52    ( ! [X1] : (r1_xboole_0(sK1,X1) | r2_hidden(sK3(k1_xboole_0,X1),X1)) ) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f475,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f485,plain,(
% 0.21/0.52    spl4_5 | spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f482,f93,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl4_5 <=> k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f482,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f38,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    ~spl4_5 | ~spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f468])).
% 0.21/0.52  fof(f468,plain,(
% 0.21/0.52    $false | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f390,f278])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),sK0) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f213,f273])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    sK0 = k1_setfam_1(k1_xboole_0) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f207,f223])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    sK0 = k8_setfam_1(sK0,k1_xboole_0) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(resolution,[],[f194,f61])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f38,f193])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f40])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(resolution,[],[f189,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f160,f188])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_10),
% 0.21/0.52    inference(forward_demodulation,[],[f122,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f39,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl4_10 <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f41,f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_5),
% 0.21/0.52    inference(forward_demodulation,[],[f91,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f38,f50])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f89])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    k1_setfam_1(k1_xboole_0) = k8_setfam_1(sK0,k1_xboole_0) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f159,f193])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(k1_xboole_0)) | (~spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f189,f193])).
% 0.21/0.52  fof(f390,plain,(
% 0.21/0.52    r1_tarski(k1_setfam_1(sK2),sK0) | ~spl4_10),
% 0.21/0.52    inference(resolution,[],[f191,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_10),
% 0.21/0.52    inference(subsumption_resolution,[],[f190,f39])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_10),
% 0.21/0.52    inference(superposition,[],[f51,f188])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.52  fof(f392,plain,(
% 0.21/0.52    ~spl4_6 | ~spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f391])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    $false | (~spl4_6 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f390,f386])).
% 0.21/0.52  fof(f386,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),sK0) | (~spl4_6 | ~spl4_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f371,f188])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_6),
% 0.21/0.52    inference(backward_demodulation,[],[f356,f352])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_6),
% 0.21/0.52    inference(resolution,[],[f326,f61])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_6),
% 0.21/0.52    inference(backward_demodulation,[],[f38,f95])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl4_6),
% 0.21/0.52    inference(forward_demodulation,[],[f41,f95])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    spl4_10 | spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f342,f124,f120])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f39,f52])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12733)------------------------------
% 0.21/0.52  % (12733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12733)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12733)Memory used [KB]: 10874
% 0.21/0.52  % (12733)Time elapsed: 0.099 s
% 0.21/0.52  % (12733)------------------------------
% 0.21/0.52  % (12733)------------------------------
% 0.21/0.52  % (12731)Success in time 0.16 s
%------------------------------------------------------------------------------
