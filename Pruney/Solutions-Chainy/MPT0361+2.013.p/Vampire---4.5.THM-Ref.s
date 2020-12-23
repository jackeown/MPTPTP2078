%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:00 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 396 expanded)
%              Number of leaves         :   37 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  370 (1211 expanded)
%              Number of equality atoms :   46 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4756,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f116,f118,f169,f174,f186,f198,f424,f438,f495,f546,f554,f815,f927,f1219,f1232,f2451,f4657])).

fof(f4657,plain,(
    spl5_207 ),
    inference(avatar_contradiction_clause,[],[f4656])).

fof(f4656,plain,
    ( $false
    | spl5_207 ),
    inference(subsumption_resolution,[],[f4655,f62])).

fof(f62,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f7,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f4655,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(sK1))
    | spl5_207 ),
    inference(forward_demodulation,[],[f4654,f4595])).

fof(f4595,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f163,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f163,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f100,f62,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f100,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f4654,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK1)))
    | spl5_207 ),
    inference(forward_demodulation,[],[f4631,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f4631,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k1_xboole_0)))
    | spl5_207 ),
    inference(backward_demodulation,[],[f2450,f4607])).

fof(f4607,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f4599,f4595])).

fof(f4599,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f2038,f4596])).

fof(f4596,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f163,f143])).

fof(f143,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = k4_xboole_0(X3,X2)
      | ~ r1_tarski(X2,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f44,f49])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2038,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2034,f1681])).

fof(f1681,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f220,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f220,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f42,f62,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2034,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
      | ~ m1_subset_1(k4_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f568,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f568,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f560,f398])).

fof(f398,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f41,f51])).

fof(f560,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2450,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))))
    | spl5_207 ),
    inference(avatar_component_clause,[],[f2448])).

fof(f2448,plain,
    ( spl5_207
  <=> sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f2451,plain,
    ( ~ spl5_207
    | ~ spl5_11
    | spl5_131 ),
    inference(avatar_split_clause,[],[f2446,f1229,f195,f2448])).

fof(f195,plain,
    ( spl5_11
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1229,plain,
    ( spl5_131
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f2446,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))))
    | ~ spl5_11
    | spl5_131 ),
    inference(forward_demodulation,[],[f2445,f43])).

fof(f2445,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)))))
    | ~ spl5_11
    | spl5_131 ),
    inference(forward_demodulation,[],[f2389,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2389,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK2))))
    | ~ spl5_11
    | spl5_131 ),
    inference(unit_resulting_resolution,[],[f1231,f2258,f53])).

fof(f2258,plain,
    ( ! [X0] : r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(X0,sK2))))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f62,f2177,f54])).

fof(f2177,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(X0,sK2)))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f2164,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2164,plain,
    ( ! [X27] : r1_tarski(k4_xboole_0(X27,sK1),k4_xboole_0(X27,sK2))
    | ~ spl5_11 ),
    inference(superposition,[],[f645,f197])).

fof(f197,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f195])).

fof(f645,plain,(
    ! [X10,X11,X9] : r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f42,f59])).

fof(f1231,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK1)
    | spl5_131 ),
    inference(avatar_component_clause,[],[f1229])).

fof(f1232,plain,
    ( ~ spl5_131
    | spl5_74
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f1206,f924,f812,f1229])).

fof(f812,plain,
    ( spl5_74
  <=> r1_tarski(k4_xboole_0(k4_subset_1(sK1,sK2,sK3),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f924,plain,
    ( spl5_84
  <=> k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1206,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK1)
    | spl5_74
    | ~ spl5_84 ),
    inference(backward_demodulation,[],[f814,f926])).

fof(f926,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f924])).

fof(f814,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_subset_1(sK1,sK2,sK3),sK3),sK1)
    | spl5_74 ),
    inference(avatar_component_clause,[],[f812])).

fof(f1219,plain,
    ( spl5_45
    | ~ spl5_84 ),
    inference(avatar_contradiction_clause,[],[f1218])).

fof(f1218,plain,
    ( $false
    | spl5_45
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1198,f645])).

fof(f1198,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | spl5_45
    | ~ spl5_84 ),
    inference(backward_demodulation,[],[f494,f926])).

fof(f494,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | spl5_45 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl5_45
  <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f927,plain,
    ( spl5_84
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f861,f74,f69,f924])).

fof(f69,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f74,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f861,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f76,f71,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f815,plain,
    ( ~ spl5_74
    | ~ spl5_9
    | spl5_51 ),
    inference(avatar_split_clause,[],[f807,f551,f183,f812])).

fof(f183,plain,
    ( spl5_9
  <=> sK1 = k2_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f551,plain,
    ( spl5_51
  <=> r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f807,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_subset_1(sK1,sK2,sK3),sK3),sK1)
    | ~ spl5_9
    | spl5_51 ),
    inference(unit_resulting_resolution,[],[f553,f351])).

fof(f351,plain,
    ( ! [X26] :
        ( ~ r1_tarski(k4_xboole_0(X26,sK3),sK1)
        | r1_tarski(X26,sK1) )
    | ~ spl5_9 ),
    inference(superposition,[],[f60,f185])).

fof(f185,plain,
    ( sK1 = k2_xboole_0(sK3,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f183])).

fof(f553,plain,
    ( ~ r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1)
    | spl5_51 ),
    inference(avatar_component_clause,[],[f551])).

fof(f554,plain,
    ( ~ spl5_51
    | spl5_50 ),
    inference(avatar_split_clause,[],[f547,f541,f551])).

fof(f541,plain,
    ( spl5_50
  <=> r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f547,plain,
    ( ~ r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1)
    | spl5_50 ),
    inference(unit_resulting_resolution,[],[f62,f543,f54])).

fof(f543,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_50 ),
    inference(avatar_component_clause,[],[f541])).

fof(f546,plain,
    ( ~ spl5_50
    | spl5_37 ),
    inference(avatar_split_clause,[],[f545,f431,f541])).

fof(f431,plain,
    ( spl5_37
  <=> m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f545,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_37 ),
    inference(subsumption_resolution,[],[f537,f40])).

fof(f537,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_37 ),
    inference(resolution,[],[f433,f46])).

fof(f433,plain,
    ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f431])).

fof(f495,plain,
    ( ~ spl5_45
    | ~ spl5_35
    | spl5_38 ),
    inference(avatar_split_clause,[],[f480,f435,f421,f492])).

fof(f421,plain,
    ( spl5_35
  <=> k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f435,plain,
    ( spl5_38
  <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f480,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | ~ spl5_35
    | spl5_38 ),
    inference(backward_demodulation,[],[f437,f423])).

fof(f423,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f421])).

fof(f437,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | spl5_38 ),
    inference(avatar_component_clause,[],[f435])).

fof(f438,plain,
    ( ~ spl5_37
    | ~ spl5_38
    | spl5_1 ),
    inference(avatar_split_clause,[],[f399,f64,f435,f431])).

fof(f64,plain,
    ( spl5_1
  <=> r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f399,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_1 ),
    inference(superposition,[],[f66,f51])).

fof(f66,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f424,plain,
    ( spl5_35
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f395,f74,f421])).

fof(f395,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f76,f51])).

fof(f198,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f193,f171,f195])).

fof(f171,plain,
    ( spl5_7
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f193,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f173,f49])).

fof(f173,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f186,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f181,f166,f183])).

fof(f166,plain,
    ( spl5_6
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f181,plain,
    ( sK1 = k2_xboole_0(sK3,sK1)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f168,f49])).

fof(f168,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f166])).

fof(f174,plain,
    ( spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f161,f106,f171])).

fof(f106,plain,
    ( spl5_4
  <=> r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f161,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f108,f62,f53])).

fof(f108,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f169,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f162,f111,f166])).

fof(f111,plain,
    ( spl5_5
  <=> r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f162,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f113,f62,f53])).

fof(f113,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f117,f74,f106])).

fof(f117,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f102,f40])).

fof(f102,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f45,f76])).

fof(f116,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f115,f69,f111])).

fof(f115,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f101,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f71])).

fof(f77,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n011.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 09:25:12 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.30  % (28442)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.10/0.33  % (28457)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.10/0.34  % (28456)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.10/0.34  % (28438)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.10/0.34  % (28449)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.10/0.34  % (28451)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.10/0.34  % (28453)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.10/0.35  % (28437)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.10/0.35  % (28437)Refutation not found, incomplete strategy% (28437)------------------------------
% 0.10/0.35  % (28437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.35  % (28437)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.35  
% 0.10/0.35  % (28437)Memory used [KB]: 10618
% 0.10/0.35  % (28437)Time elapsed: 0.057 s
% 0.10/0.35  % (28437)------------------------------
% 0.10/0.35  % (28437)------------------------------
% 0.10/0.35  % (28455)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.10/0.35  % (28454)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.10/0.35  % (28450)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.10/0.35  % (28458)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.10/0.35  % (28436)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.10/0.36  % (28439)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.10/0.36  % (28441)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.10/0.36  % (28448)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.10/0.37  % (28447)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.10/0.37  % (28445)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.10/0.38  % (28452)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.10/0.38  % (28459)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.10/0.38  % (28459)Refutation not found, incomplete strategy% (28459)------------------------------
% 0.10/0.38  % (28459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.38  % (28459)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.38  
% 0.10/0.38  % (28459)Memory used [KB]: 10490
% 0.10/0.38  % (28459)Time elapsed: 0.088 s
% 0.10/0.38  % (28459)------------------------------
% 0.10/0.38  % (28459)------------------------------
% 0.10/0.39  % (28443)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 2.28/0.56  % (28455)Refutation found. Thanks to Tanya!
% 2.28/0.56  % SZS status Theorem for theBenchmark
% 2.28/0.56  % SZS output start Proof for theBenchmark
% 2.28/0.56  fof(f4756,plain,(
% 2.28/0.56    $false),
% 2.28/0.56    inference(avatar_sat_refutation,[],[f67,f72,f77,f116,f118,f169,f174,f186,f198,f424,f438,f495,f546,f554,f815,f927,f1219,f1232,f2451,f4657])).
% 2.28/0.56  fof(f4657,plain,(
% 2.28/0.56    spl5_207),
% 2.28/0.56    inference(avatar_contradiction_clause,[],[f4656])).
% 2.28/0.56  fof(f4656,plain,(
% 2.28/0.56    $false | spl5_207),
% 2.28/0.56    inference(subsumption_resolution,[],[f4655,f62])).
% 2.28/0.56  fof(f62,plain,(
% 2.28/0.56    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(equality_resolution,[],[f57])).
% 2.28/0.56  fof(f57,plain,(
% 2.28/0.56    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.28/0.56    inference(cnf_transformation,[],[f36])).
% 2.28/0.56  fof(f36,plain,(
% 2.28/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 2.28/0.56    inference(nnf_transformation,[],[f27])).
% 2.28/0.56  fof(f27,plain,(
% 2.28/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 2.28/0.56    inference(definition_folding,[],[f7,f26])).
% 2.28/0.56  fof(f26,plain,(
% 2.28/0.56    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.28/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.28/0.56  fof(f7,axiom,(
% 2.28/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.28/0.56  fof(f4655,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(sK1)) | spl5_207),
% 2.28/0.56    inference(forward_demodulation,[],[f4654,f4595])).
% 2.28/0.56  fof(f4595,plain,(
% 2.28/0.56    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f163,f49])).
% 2.28/0.56  fof(f49,plain,(
% 2.28/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f19])).
% 2.28/0.56  fof(f19,plain,(
% 2.28/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.28/0.56    inference(ennf_transformation,[],[f2])).
% 2.28/0.56  fof(f2,axiom,(
% 2.28/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.28/0.56  fof(f163,plain,(
% 2.28/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f100,f62,f53])).
% 2.28/0.56  fof(f53,plain,(
% 2.28/0.56    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f35])).
% 2.28/0.56  fof(f35,plain,(
% 2.28/0.56    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.28/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 2.28/0.56  fof(f34,plain,(
% 2.28/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.28/0.56    introduced(choice_axiom,[])).
% 2.28/0.56  fof(f33,plain,(
% 2.28/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.28/0.56    inference(rectify,[],[f32])).
% 2.28/0.56  fof(f32,plain,(
% 2.28/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.28/0.56    inference(nnf_transformation,[],[f26])).
% 2.28/0.56  fof(f100,plain,(
% 2.28/0.56    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f40,f41,f45])).
% 2.28/0.56  fof(f45,plain,(
% 2.28/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f31])).
% 2.28/0.56  fof(f31,plain,(
% 2.28/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.28/0.56    inference(nnf_transformation,[],[f18])).
% 2.28/0.56  fof(f18,plain,(
% 2.28/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.28/0.56    inference(ennf_transformation,[],[f8])).
% 2.28/0.56  fof(f8,axiom,(
% 2.28/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.28/0.56  fof(f41,plain,(
% 2.28/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f14])).
% 2.28/0.56  fof(f14,axiom,(
% 2.28/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.28/0.56  fof(f40,plain,(
% 2.28/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f11])).
% 2.28/0.56  fof(f11,axiom,(
% 2.28/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.28/0.56  fof(f4654,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK1))) | spl5_207),
% 2.28/0.56    inference(forward_demodulation,[],[f4631,f43])).
% 2.28/0.56  fof(f43,plain,(
% 2.28/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f1])).
% 2.28/0.56  fof(f1,axiom,(
% 2.28/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.28/0.56  fof(f4631,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k1_xboole_0))) | spl5_207),
% 2.28/0.56    inference(backward_demodulation,[],[f2450,f4607])).
% 2.28/0.56  fof(f4607,plain,(
% 2.28/0.56    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.28/0.56    inference(backward_demodulation,[],[f4599,f4595])).
% 2.28/0.56  fof(f4599,plain,(
% 2.28/0.56    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) )),
% 2.28/0.56    inference(backward_demodulation,[],[f2038,f4596])).
% 2.28/0.56  fof(f4596,plain,(
% 2.28/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f163,f143])).
% 2.28/0.56  fof(f143,plain,(
% 2.28/0.56    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k4_xboole_0(X3,X2) | ~r1_tarski(X2,k4_xboole_0(X3,X2))) )),
% 2.28/0.56    inference(superposition,[],[f44,f49])).
% 2.28/0.56  fof(f44,plain,(
% 2.28/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f4])).
% 2.28/0.56  fof(f4,axiom,(
% 2.28/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.28/0.56  fof(f2038,plain,(
% 2.28/0.56    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 2.28/0.56    inference(subsumption_resolution,[],[f2034,f1681])).
% 2.28/0.56  fof(f1681,plain,(
% 2.28/0.56    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f40,f220,f46])).
% 2.28/0.56  fof(f46,plain,(
% 2.28/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f31])).
% 2.28/0.56  fof(f220,plain,(
% 2.28/0.56    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f42,f62,f54])).
% 2.28/0.56  fof(f54,plain,(
% 2.28/0.56    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X3,X0) | r2_hidden(X3,X1)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f35])).
% 2.28/0.56  fof(f42,plain,(
% 2.28/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f3])).
% 2.28/0.56  fof(f3,axiom,(
% 2.28/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.28/0.56  fof(f2034,plain,(
% 2.28/0.56    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) | ~m1_subset_1(k4_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1))) )),
% 2.28/0.56    inference(superposition,[],[f568,f51])).
% 2.28/0.56  fof(f51,plain,(
% 2.28/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f21])).
% 2.28/0.56  fof(f21,plain,(
% 2.28/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.56    inference(ennf_transformation,[],[f9])).
% 2.28/0.56  fof(f9,axiom,(
% 2.28/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.28/0.56  fof(f568,plain,(
% 2.28/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.28/0.56    inference(forward_demodulation,[],[f560,f398])).
% 2.28/0.56  fof(f398,plain,(
% 2.28/0.56    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f41,f51])).
% 2.28/0.56  fof(f560,plain,(
% 2.28/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f41,f52])).
% 2.28/0.56  fof(f52,plain,(
% 2.28/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f22])).
% 2.28/0.56  fof(f22,plain,(
% 2.28/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.56    inference(ennf_transformation,[],[f12])).
% 2.28/0.56  fof(f12,axiom,(
% 2.28/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.28/0.56  fof(f2450,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))))) | spl5_207),
% 2.28/0.56    inference(avatar_component_clause,[],[f2448])).
% 2.28/0.56  fof(f2448,plain,(
% 2.28/0.56    spl5_207 <=> sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))))),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).
% 2.28/0.56  fof(f2451,plain,(
% 2.28/0.56    ~spl5_207 | ~spl5_11 | spl5_131),
% 2.28/0.56    inference(avatar_split_clause,[],[f2446,f1229,f195,f2448])).
% 2.28/0.56  fof(f195,plain,(
% 2.28/0.56    spl5_11 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.28/0.56  fof(f1229,plain,(
% 2.28/0.56    spl5_131 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK1)),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).
% 2.28/0.56  fof(f2446,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))))) | (~spl5_11 | spl5_131)),
% 2.28/0.56    inference(forward_demodulation,[],[f2445,f43])).
% 2.28/0.56  fof(f2445,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2))))) | (~spl5_11 | spl5_131)),
% 2.28/0.56    inference(forward_demodulation,[],[f2389,f59])).
% 2.28/0.56  fof(f59,plain,(
% 2.28/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f5])).
% 2.28/0.56  fof(f5,axiom,(
% 2.28/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.28/0.56  fof(f2389,plain,(
% 2.28/0.56    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK2)))) | (~spl5_11 | spl5_131)),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f1231,f2258,f53])).
% 2.28/0.56  fof(f2258,plain,(
% 2.28/0.56    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(X0,sK2))))) ) | ~spl5_11),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f62,f2177,f54])).
% 2.28/0.56  fof(f2177,plain,(
% 2.28/0.56    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(X0,sK2)))) ) | ~spl5_11),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f2164,f60])).
% 2.28/0.56  fof(f60,plain,(
% 2.28/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.28/0.56    inference(cnf_transformation,[],[f23])).
% 2.28/0.56  fof(f23,plain,(
% 2.28/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.28/0.56    inference(ennf_transformation,[],[f6])).
% 2.28/0.56  fof(f6,axiom,(
% 2.28/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.28/0.56  fof(f2164,plain,(
% 2.28/0.56    ( ! [X27] : (r1_tarski(k4_xboole_0(X27,sK1),k4_xboole_0(X27,sK2))) ) | ~spl5_11),
% 2.28/0.56    inference(superposition,[],[f645,f197])).
% 2.28/0.56  fof(f197,plain,(
% 2.28/0.56    sK1 = k2_xboole_0(sK2,sK1) | ~spl5_11),
% 2.28/0.56    inference(avatar_component_clause,[],[f195])).
% 2.28/0.56  fof(f645,plain,(
% 2.28/0.56    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10))) )),
% 2.28/0.56    inference(superposition,[],[f42,f59])).
% 2.28/0.56  fof(f1231,plain,(
% 2.28/0.56    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK1) | spl5_131),
% 2.28/0.56    inference(avatar_component_clause,[],[f1229])).
% 2.28/0.56  fof(f1232,plain,(
% 2.28/0.56    ~spl5_131 | spl5_74 | ~spl5_84),
% 2.28/0.56    inference(avatar_split_clause,[],[f1206,f924,f812,f1229])).
% 2.28/0.56  fof(f812,plain,(
% 2.28/0.56    spl5_74 <=> r1_tarski(k4_xboole_0(k4_subset_1(sK1,sK2,sK3),sK3),sK1)),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 2.28/0.56  fof(f924,plain,(
% 2.28/0.56    spl5_84 <=> k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 2.28/0.56  fof(f1206,plain,(
% 2.28/0.56    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK3),sK1) | (spl5_74 | ~spl5_84)),
% 2.28/0.56    inference(backward_demodulation,[],[f814,f926])).
% 2.28/0.56  fof(f926,plain,(
% 2.28/0.56    k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) | ~spl5_84),
% 2.28/0.56    inference(avatar_component_clause,[],[f924])).
% 2.28/0.56  fof(f814,plain,(
% 2.28/0.56    ~r1_tarski(k4_xboole_0(k4_subset_1(sK1,sK2,sK3),sK3),sK1) | spl5_74),
% 2.28/0.56    inference(avatar_component_clause,[],[f812])).
% 2.28/0.56  fof(f1219,plain,(
% 2.28/0.56    spl5_45 | ~spl5_84),
% 2.28/0.56    inference(avatar_contradiction_clause,[],[f1218])).
% 2.28/0.56  fof(f1218,plain,(
% 2.28/0.56    $false | (spl5_45 | ~spl5_84)),
% 2.28/0.56    inference(subsumption_resolution,[],[f1198,f645])).
% 2.28/0.56  fof(f1198,plain,(
% 2.28/0.56    ~r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) | (spl5_45 | ~spl5_84)),
% 2.28/0.56    inference(backward_demodulation,[],[f494,f926])).
% 2.28/0.56  fof(f494,plain,(
% 2.28/0.56    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) | spl5_45),
% 2.28/0.56    inference(avatar_component_clause,[],[f492])).
% 2.28/0.56  fof(f492,plain,(
% 2.28/0.56    spl5_45 <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.28/0.56  fof(f927,plain,(
% 2.28/0.56    spl5_84 | ~spl5_2 | ~spl5_3),
% 2.28/0.56    inference(avatar_split_clause,[],[f861,f74,f69,f924])).
% 2.28/0.56  fof(f69,plain,(
% 2.28/0.56    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.28/0.56  fof(f74,plain,(
% 2.28/0.56    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.28/0.56  fof(f861,plain,(
% 2.28/0.56    k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) | (~spl5_2 | ~spl5_3)),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f76,f71,f61])).
% 2.28/0.56  fof(f61,plain,(
% 2.28/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.56    inference(cnf_transformation,[],[f25])).
% 2.28/0.56  fof(f25,plain,(
% 2.28/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.56    inference(flattening,[],[f24])).
% 2.28/0.56  fof(f24,plain,(
% 2.28/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.28/0.56    inference(ennf_transformation,[],[f13])).
% 2.28/0.56  fof(f13,axiom,(
% 2.28/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.28/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.28/0.56  fof(f71,plain,(
% 2.28/0.56    m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.28/0.56    inference(avatar_component_clause,[],[f69])).
% 2.28/0.56  fof(f76,plain,(
% 2.28/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.28/0.56    inference(avatar_component_clause,[],[f74])).
% 2.28/0.56  fof(f815,plain,(
% 2.28/0.56    ~spl5_74 | ~spl5_9 | spl5_51),
% 2.28/0.56    inference(avatar_split_clause,[],[f807,f551,f183,f812])).
% 2.28/0.56  fof(f183,plain,(
% 2.28/0.56    spl5_9 <=> sK1 = k2_xboole_0(sK3,sK1)),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.28/0.56  fof(f551,plain,(
% 2.28/0.56    spl5_51 <=> r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1)),
% 2.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.28/0.56  fof(f807,plain,(
% 2.28/0.56    ~r1_tarski(k4_xboole_0(k4_subset_1(sK1,sK2,sK3),sK3),sK1) | (~spl5_9 | spl5_51)),
% 2.28/0.56    inference(unit_resulting_resolution,[],[f553,f351])).
% 2.28/0.56  fof(f351,plain,(
% 2.28/0.56    ( ! [X26] : (~r1_tarski(k4_xboole_0(X26,sK3),sK1) | r1_tarski(X26,sK1)) ) | ~spl5_9),
% 2.28/0.56    inference(superposition,[],[f60,f185])).
% 2.28/0.56  fof(f185,plain,(
% 2.28/0.56    sK1 = k2_xboole_0(sK3,sK1) | ~spl5_9),
% 2.28/0.56    inference(avatar_component_clause,[],[f183])).
% 2.28/0.56  fof(f553,plain,(
% 2.28/0.56    ~r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1) | spl5_51),
% 2.28/0.56    inference(avatar_component_clause,[],[f551])).
% 2.28/0.56  fof(f554,plain,(
% 2.28/0.56    ~spl5_51 | spl5_50),
% 2.28/0.56    inference(avatar_split_clause,[],[f547,f541,f551])).
% 2.28/0.56  fof(f541,plain,(
% 2.28/0.56    spl5_50 <=> r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 2.28/0.57  fof(f547,plain,(
% 2.28/0.57    ~r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1) | spl5_50),
% 2.28/0.57    inference(unit_resulting_resolution,[],[f62,f543,f54])).
% 2.28/0.57  fof(f543,plain,(
% 2.28/0.57    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_50),
% 2.28/0.57    inference(avatar_component_clause,[],[f541])).
% 2.28/0.57  fof(f546,plain,(
% 2.28/0.57    ~spl5_50 | spl5_37),
% 2.28/0.57    inference(avatar_split_clause,[],[f545,f431,f541])).
% 2.28/0.57  fof(f431,plain,(
% 2.28/0.57    spl5_37 <=> m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.28/0.57  fof(f545,plain,(
% 2.28/0.57    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_37),
% 2.28/0.57    inference(subsumption_resolution,[],[f537,f40])).
% 2.28/0.57  fof(f537,plain,(
% 2.28/0.57    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_37),
% 2.28/0.57    inference(resolution,[],[f433,f46])).
% 2.28/0.57  fof(f433,plain,(
% 2.28/0.57    ~m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_37),
% 2.28/0.57    inference(avatar_component_clause,[],[f431])).
% 2.28/0.57  fof(f495,plain,(
% 2.28/0.57    ~spl5_45 | ~spl5_35 | spl5_38),
% 2.28/0.57    inference(avatar_split_clause,[],[f480,f435,f421,f492])).
% 2.28/0.57  fof(f421,plain,(
% 2.28/0.57    spl5_35 <=> k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.28/0.57  fof(f435,plain,(
% 2.28/0.57    spl5_38 <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.28/0.57  fof(f480,plain,(
% 2.28/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) | (~spl5_35 | spl5_38)),
% 2.28/0.57    inference(backward_demodulation,[],[f437,f423])).
% 2.28/0.57  fof(f423,plain,(
% 2.28/0.57    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_35),
% 2.28/0.57    inference(avatar_component_clause,[],[f421])).
% 2.28/0.57  fof(f437,plain,(
% 2.28/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | spl5_38),
% 2.28/0.57    inference(avatar_component_clause,[],[f435])).
% 2.28/0.57  fof(f438,plain,(
% 2.28/0.57    ~spl5_37 | ~spl5_38 | spl5_1),
% 2.28/0.57    inference(avatar_split_clause,[],[f399,f64,f435,f431])).
% 2.28/0.57  fof(f64,plain,(
% 2.28/0.57    spl5_1 <=> r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.28/0.57  fof(f399,plain,(
% 2.28/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | ~m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_1),
% 2.28/0.57    inference(superposition,[],[f66,f51])).
% 2.28/0.57  fof(f66,plain,(
% 2.28/0.57    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | spl5_1),
% 2.28/0.57    inference(avatar_component_clause,[],[f64])).
% 2.28/0.57  fof(f424,plain,(
% 2.28/0.57    spl5_35 | ~spl5_3),
% 2.28/0.57    inference(avatar_split_clause,[],[f395,f74,f421])).
% 2.28/0.57  fof(f395,plain,(
% 2.28/0.57    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_3),
% 2.28/0.57    inference(unit_resulting_resolution,[],[f76,f51])).
% 2.28/0.57  fof(f198,plain,(
% 2.28/0.57    spl5_11 | ~spl5_7),
% 2.28/0.57    inference(avatar_split_clause,[],[f193,f171,f195])).
% 2.28/0.57  fof(f171,plain,(
% 2.28/0.57    spl5_7 <=> r1_tarski(sK2,sK1)),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.28/0.57  fof(f193,plain,(
% 2.28/0.57    sK1 = k2_xboole_0(sK2,sK1) | ~spl5_7),
% 2.28/0.57    inference(unit_resulting_resolution,[],[f173,f49])).
% 2.28/0.57  fof(f173,plain,(
% 2.28/0.57    r1_tarski(sK2,sK1) | ~spl5_7),
% 2.28/0.57    inference(avatar_component_clause,[],[f171])).
% 2.28/0.57  fof(f186,plain,(
% 2.28/0.57    spl5_9 | ~spl5_6),
% 2.28/0.57    inference(avatar_split_clause,[],[f181,f166,f183])).
% 2.28/0.57  fof(f166,plain,(
% 2.28/0.57    spl5_6 <=> r1_tarski(sK3,sK1)),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.28/0.57  fof(f181,plain,(
% 2.28/0.57    sK1 = k2_xboole_0(sK3,sK1) | ~spl5_6),
% 2.28/0.57    inference(unit_resulting_resolution,[],[f168,f49])).
% 2.28/0.57  fof(f168,plain,(
% 2.28/0.57    r1_tarski(sK3,sK1) | ~spl5_6),
% 2.28/0.57    inference(avatar_component_clause,[],[f166])).
% 2.28/0.57  fof(f174,plain,(
% 2.28/0.57    spl5_7 | ~spl5_4),
% 2.28/0.57    inference(avatar_split_clause,[],[f161,f106,f171])).
% 2.28/0.57  fof(f106,plain,(
% 2.28/0.57    spl5_4 <=> r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.28/0.57  fof(f161,plain,(
% 2.28/0.57    r1_tarski(sK2,sK1) | ~spl5_4),
% 2.28/0.57    inference(unit_resulting_resolution,[],[f108,f62,f53])).
% 2.28/0.57  fof(f108,plain,(
% 2.28/0.57    r2_hidden(sK2,k1_zfmisc_1(sK1)) | ~spl5_4),
% 2.28/0.57    inference(avatar_component_clause,[],[f106])).
% 2.28/0.57  fof(f169,plain,(
% 2.28/0.57    spl5_6 | ~spl5_5),
% 2.28/0.57    inference(avatar_split_clause,[],[f162,f111,f166])).
% 2.28/0.57  fof(f111,plain,(
% 2.28/0.57    spl5_5 <=> r2_hidden(sK3,k1_zfmisc_1(sK1))),
% 2.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.28/0.57  fof(f162,plain,(
% 2.28/0.57    r1_tarski(sK3,sK1) | ~spl5_5),
% 2.28/0.57    inference(unit_resulting_resolution,[],[f113,f62,f53])).
% 2.28/0.57  fof(f113,plain,(
% 2.28/0.57    r2_hidden(sK3,k1_zfmisc_1(sK1)) | ~spl5_5),
% 2.28/0.57    inference(avatar_component_clause,[],[f111])).
% 2.28/0.57  fof(f118,plain,(
% 2.28/0.57    spl5_4 | ~spl5_3),
% 2.28/0.57    inference(avatar_split_clause,[],[f117,f74,f106])).
% 2.28/0.57  fof(f117,plain,(
% 2.28/0.57    r2_hidden(sK2,k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.28/0.57    inference(subsumption_resolution,[],[f102,f40])).
% 2.28/0.57  fof(f102,plain,(
% 2.28/0.57    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.28/0.57    inference(resolution,[],[f45,f76])).
% 2.28/0.57  fof(f116,plain,(
% 2.28/0.57    spl5_5 | ~spl5_2),
% 2.28/0.57    inference(avatar_split_clause,[],[f115,f69,f111])).
% 2.28/0.57  fof(f115,plain,(
% 2.28/0.57    r2_hidden(sK3,k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.28/0.57    inference(subsumption_resolution,[],[f101,f40])).
% 2.28/0.57  fof(f101,plain,(
% 2.28/0.57    r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.28/0.57    inference(resolution,[],[f45,f71])).
% 2.28/0.57  fof(f77,plain,(
% 2.28/0.57    spl5_3),
% 2.28/0.57    inference(avatar_split_clause,[],[f37,f74])).
% 2.28/0.57  fof(f37,plain,(
% 2.28/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.57    inference(cnf_transformation,[],[f30])).
% 2.28/0.57  fof(f30,plain,(
% 2.28/0.57    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f29,f28])).
% 2.28/0.57  fof(f28,plain,(
% 2.28/0.57    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.28/0.57    introduced(choice_axiom,[])).
% 2.28/0.57  fof(f29,plain,(
% 2.28/0.57    ? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 2.28/0.57    introduced(choice_axiom,[])).
% 2.28/0.57  fof(f17,plain,(
% 2.28/0.57    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.57    inference(ennf_transformation,[],[f16])).
% 2.28/0.57  fof(f16,negated_conjecture,(
% 2.28/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.28/0.57    inference(negated_conjecture,[],[f15])).
% 2.28/0.57  fof(f15,conjecture,(
% 2.28/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.28/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 2.28/0.57  fof(f72,plain,(
% 2.28/0.57    spl5_2),
% 2.28/0.57    inference(avatar_split_clause,[],[f38,f69])).
% 2.28/0.57  fof(f38,plain,(
% 2.28/0.57    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.28/0.57    inference(cnf_transformation,[],[f30])).
% 2.28/0.57  fof(f67,plain,(
% 2.28/0.57    ~spl5_1),
% 2.28/0.57    inference(avatar_split_clause,[],[f39,f64])).
% 2.28/0.57  fof(f39,plain,(
% 2.28/0.57    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.28/0.57    inference(cnf_transformation,[],[f30])).
% 2.28/0.57  % SZS output end Proof for theBenchmark
% 2.28/0.57  % (28455)------------------------------
% 2.28/0.57  % (28455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.57  % (28455)Termination reason: Refutation
% 2.28/0.57  
% 2.28/0.57  % (28455)Memory used [KB]: 13688
% 2.28/0.57  % (28455)Time elapsed: 0.261 s
% 2.28/0.57  % (28455)------------------------------
% 2.28/0.57  % (28455)------------------------------
% 2.28/0.57  % (28430)Success in time 0.295 s
%------------------------------------------------------------------------------
