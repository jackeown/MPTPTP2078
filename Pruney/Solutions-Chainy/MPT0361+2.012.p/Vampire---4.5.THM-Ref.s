%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 374 expanded)
%              Number of leaves         :   38 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  370 (1121 expanded)
%              Number of equality atoms :   43 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f123,f125,f215,f220,f265,f796,f820,f882,f1172,f1434,f1858,f1865,f1978,f3350,f3636,f8148])).

fof(f8148,plain,(
    spl5_318 ),
    inference(avatar_contradiction_clause,[],[f8147])).

fof(f8147,plain,
    ( $false
    | spl5_318 ),
    inference(subsumption_resolution,[],[f8146,f65])).

fof(f65,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f8,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f8146,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(sK1))
    | spl5_318 ),
    inference(forward_demodulation,[],[f8145,f7662])).

fof(f7662,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f209,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f209,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f107,f65,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f107,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f42,f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f8145,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK1)))
    | spl5_318 ),
    inference(forward_demodulation,[],[f8082,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f8082,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k1_xboole_0)))
    | spl5_318 ),
    inference(backward_demodulation,[],[f3635,f8001])).

fof(f8001,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f7730,f7662])).

fof(f7730,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f2846,f7722])).

fof(f7722,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f209,f149])).

fof(f149,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = k4_xboole_0(X3,X2)
      | ~ r1_tarski(X2,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f46,f51])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2846,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2838,f961])).

fof(f961,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f955,f775])).

fof(f775,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f955,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2838,plain,(
    ! [X0] : k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f786,f53])).

fof(f786,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f410,f775])).

fof(f410,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3635,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))))
    | spl5_318 ),
    inference(avatar_component_clause,[],[f3633])).

fof(f3633,plain,
    ( spl5_318
  <=> sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_318])])).

fof(f3636,plain,
    ( ~ spl5_318
    | ~ spl5_6
    | spl5_296 ),
    inference(avatar_split_clause,[],[f3631,f3347,f212,f3633])).

fof(f212,plain,
    ( spl5_6
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f3347,plain,
    ( spl5_296
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_296])])).

fof(f3631,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))))
    | ~ spl5_6
    | spl5_296 ),
    inference(forward_demodulation,[],[f3588,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3588,plain,
    ( ~ sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK3))))
    | ~ spl5_6
    | spl5_296 ),
    inference(unit_resulting_resolution,[],[f3349,f2192,f55])).

fof(f2192,plain,
    ( ! [X0] : r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(X0,sK3))))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f65,f2100,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2100,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(X0,sK3)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f476,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f476,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK3))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f214,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f214,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f212])).

fof(f3349,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1)
    | spl5_296 ),
    inference(avatar_component_clause,[],[f3347])).

fof(f3350,plain,
    ( ~ spl5_296
    | ~ spl5_14
    | spl5_214 ),
    inference(avatar_split_clause,[],[f3341,f1975,f262,f3347])).

fof(f262,plain,
    ( spl5_14
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1975,plain,
    ( spl5_214
  <=> r1_tarski(k2_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f3341,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1)
    | ~ spl5_14
    | spl5_214 ),
    inference(unit_resulting_resolution,[],[f1977,f665])).

fof(f665,plain,
    ( ! [X18] :
        ( ~ r1_tarski(k4_xboole_0(X18,sK2),sK1)
        | r1_tarski(X18,sK1) )
    | ~ spl5_14 ),
    inference(superposition,[],[f63,f264])).

fof(f264,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1977,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | spl5_214 ),
    inference(avatar_component_clause,[],[f1975])).

fof(f1978,plain,
    ( ~ spl5_214
    | spl5_201 ),
    inference(avatar_split_clause,[],[f1961,f1855,f1975])).

fof(f1855,plain,
    ( spl5_201
  <=> r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f1961,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | spl5_201 ),
    inference(unit_resulting_resolution,[],[f65,f1857,f56])).

fof(f1857,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_201 ),
    inference(avatar_component_clause,[],[f1855])).

fof(f1865,plain,
    ( spl5_86
    | ~ spl5_130 ),
    inference(avatar_contradiction_clause,[],[f1864])).

fof(f1864,plain,
    ( $false
    | spl5_86
    | ~ spl5_130 ),
    inference(subsumption_resolution,[],[f1851,f471])).

fof(f471,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1851,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | spl5_86
    | ~ spl5_130 ),
    inference(backward_demodulation,[],[f881,f1433])).

fof(f1433,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_130 ),
    inference(avatar_component_clause,[],[f1431])).

fof(f1431,plain,
    ( spl5_130
  <=> k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f881,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | spl5_86 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl5_86
  <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f1858,plain,
    ( ~ spl5_201
    | spl5_109
    | ~ spl5_130 ),
    inference(avatar_split_clause,[],[f1848,f1431,f1167,f1855])).

fof(f1167,plain,
    ( spl5_109
  <=> r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1848,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_109
    | ~ spl5_130 ),
    inference(backward_demodulation,[],[f1169,f1433])).

fof(f1169,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_109 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1434,plain,
    ( spl5_130
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1359,f77,f72,f1431])).

fof(f72,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f77,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1359,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f79,f74,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f1172,plain,
    ( ~ spl5_109
    | spl5_77 ),
    inference(avatar_split_clause,[],[f1171,f813,f1167])).

fof(f813,plain,
    ( spl5_77
  <=> m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1171,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_77 ),
    inference(subsumption_resolution,[],[f1163,f42])).

fof(f1163,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_77 ),
    inference(resolution,[],[f815,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f815,plain,
    ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_77 ),
    inference(avatar_component_clause,[],[f813])).

fof(f882,plain,
    ( ~ spl5_86
    | ~ spl5_73
    | spl5_78 ),
    inference(avatar_split_clause,[],[f864,f817,f793,f879])).

fof(f793,plain,
    ( spl5_73
  <=> k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f817,plain,
    ( spl5_78
  <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f864,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | ~ spl5_73
    | spl5_78 ),
    inference(backward_demodulation,[],[f819,f795])).

fof(f795,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f793])).

fof(f819,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | spl5_78 ),
    inference(avatar_component_clause,[],[f817])).

fof(f820,plain,
    ( ~ spl5_77
    | ~ spl5_78
    | spl5_1 ),
    inference(avatar_split_clause,[],[f776,f67,f817,f813])).

fof(f67,plain,
    ( spl5_1
  <=> r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f776,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_1 ),
    inference(superposition,[],[f69,f53])).

fof(f69,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f796,plain,
    ( spl5_73
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f773,f77,f793])).

fof(f773,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f79,f53])).

fof(f265,plain,
    ( spl5_14
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f260,f217,f262])).

fof(f217,plain,
    ( spl5_7
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f260,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f219,f51])).

fof(f219,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f220,plain,
    ( spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f207,f113,f217])).

fof(f113,plain,
    ( spl5_4
  <=> r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f207,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f115,f65,f55])).

fof(f115,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f215,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f208,f118,f212])).

fof(f118,plain,
    ( spl5_5
  <=> r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f208,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f120,f65,f55])).

fof(f120,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f124,f77,f113])).

fof(f124,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f109,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f47,f79])).

fof(f123,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f122,f72,f118])).

fof(f122,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f108,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f74])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f41,f67])).

fof(f41,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (24031)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (24027)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (24041)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (24037)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (24044)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (24028)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (24039)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (24033)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (24042)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (24035)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (24032)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (24029)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (24030)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (24026)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (24038)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (24046)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (24027)Refutation not found, incomplete strategy% (24027)------------------------------
% 0.20/0.50  % (24027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24027)Memory used [KB]: 10618
% 0.20/0.50  % (24027)Time elapsed: 0.073 s
% 0.20/0.50  % (24027)------------------------------
% 0.20/0.50  % (24027)------------------------------
% 0.20/0.50  % (24046)Refutation not found, incomplete strategy% (24046)------------------------------
% 0.20/0.50  % (24046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24043)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (24046)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24046)Memory used [KB]: 10490
% 0.20/0.50  % (24046)Time elapsed: 0.104 s
% 0.20/0.50  % (24046)------------------------------
% 0.20/0.50  % (24046)------------------------------
% 0.20/0.50  % (24040)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (24034)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (24036)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (24045)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 2.91/0.74  % (24042)Refutation found. Thanks to Tanya!
% 2.91/0.74  % SZS status Theorem for theBenchmark
% 2.91/0.74  % SZS output start Proof for theBenchmark
% 2.91/0.74  fof(f8185,plain,(
% 2.91/0.74    $false),
% 2.91/0.74    inference(avatar_sat_refutation,[],[f70,f75,f80,f123,f125,f215,f220,f265,f796,f820,f882,f1172,f1434,f1858,f1865,f1978,f3350,f3636,f8148])).
% 2.91/0.74  fof(f8148,plain,(
% 2.91/0.74    spl5_318),
% 2.91/0.74    inference(avatar_contradiction_clause,[],[f8147])).
% 2.91/0.74  fof(f8147,plain,(
% 2.91/0.74    $false | spl5_318),
% 2.91/0.74    inference(subsumption_resolution,[],[f8146,f65])).
% 2.91/0.74  fof(f65,plain,(
% 2.91/0.74    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(equality_resolution,[],[f59])).
% 2.91/0.74  fof(f59,plain,(
% 2.91/0.74    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.91/0.74    inference(cnf_transformation,[],[f38])).
% 2.91/0.74  fof(f38,plain,(
% 2.91/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 2.91/0.74    inference(nnf_transformation,[],[f29])).
% 2.91/0.74  fof(f29,plain,(
% 2.91/0.74    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 2.91/0.74    inference(definition_folding,[],[f8,f28])).
% 2.91/0.74  fof(f28,plain,(
% 2.91/0.74    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.91/0.74    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.91/0.74  fof(f8,axiom,(
% 2.91/0.74    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.91/0.74  fof(f8146,plain,(
% 2.91/0.74    ~sP0(sK1,k1_zfmisc_1(sK1)) | spl5_318),
% 2.91/0.74    inference(forward_demodulation,[],[f8145,f7662])).
% 2.91/0.74  fof(f7662,plain,(
% 2.91/0.74    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f209,f51])).
% 2.91/0.74  fof(f51,plain,(
% 2.91/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f20])).
% 2.91/0.74  fof(f20,plain,(
% 2.91/0.74    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.91/0.74    inference(ennf_transformation,[],[f2])).
% 2.91/0.74  fof(f2,axiom,(
% 2.91/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.91/0.74  fof(f209,plain,(
% 2.91/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f107,f65,f55])).
% 2.91/0.74  fof(f55,plain,(
% 2.91/0.74    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f37])).
% 2.91/0.74  fof(f37,plain,(
% 2.91/0.74    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.91/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.91/0.74  fof(f36,plain,(
% 2.91/0.74    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.91/0.74    introduced(choice_axiom,[])).
% 2.91/0.74  fof(f35,plain,(
% 2.91/0.74    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.91/0.74    inference(rectify,[],[f34])).
% 2.91/0.74  fof(f34,plain,(
% 2.91/0.74    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.91/0.74    inference(nnf_transformation,[],[f28])).
% 2.91/0.74  fof(f107,plain,(
% 2.91/0.74    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f42,f43,f47])).
% 2.91/0.74  fof(f47,plain,(
% 2.91/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f33])).
% 2.91/0.74  fof(f33,plain,(
% 2.91/0.74    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.91/0.74    inference(nnf_transformation,[],[f19])).
% 2.91/0.74  fof(f19,plain,(
% 2.91/0.74    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.91/0.74    inference(ennf_transformation,[],[f9])).
% 2.91/0.74  fof(f9,axiom,(
% 2.91/0.74    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.91/0.74  fof(f43,plain,(
% 2.91/0.74    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f15])).
% 2.91/0.74  fof(f15,axiom,(
% 2.91/0.74    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.91/0.74  fof(f42,plain,(
% 2.91/0.74    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f12])).
% 2.91/0.74  fof(f12,axiom,(
% 2.91/0.74    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.91/0.74  fof(f8145,plain,(
% 2.91/0.74    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(k1_xboole_0,sK1))) | spl5_318),
% 2.91/0.74    inference(forward_demodulation,[],[f8082,f45])).
% 2.91/0.74  fof(f45,plain,(
% 2.91/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f1])).
% 2.91/0.74  fof(f1,axiom,(
% 2.91/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.91/0.74  fof(f8082,plain,(
% 2.91/0.74    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k1_xboole_0))) | spl5_318),
% 2.91/0.74    inference(backward_demodulation,[],[f3635,f8001])).
% 2.91/0.74  fof(f8001,plain,(
% 2.91/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.91/0.74    inference(backward_demodulation,[],[f7730,f7662])).
% 2.91/0.74  fof(f7730,plain,(
% 2.91/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) )),
% 2.91/0.74    inference(backward_demodulation,[],[f2846,f7722])).
% 2.91/0.74  fof(f7722,plain,(
% 2.91/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f209,f149])).
% 2.91/0.74  fof(f149,plain,(
% 2.91/0.74    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k4_xboole_0(X3,X2) | ~r1_tarski(X2,k4_xboole_0(X3,X2))) )),
% 2.91/0.74    inference(superposition,[],[f46,f51])).
% 2.91/0.74  fof(f46,plain,(
% 2.91/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f4])).
% 2.91/0.74  fof(f4,axiom,(
% 2.91/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.91/0.74  fof(f2846,plain,(
% 2.91/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.91/0.74    inference(forward_demodulation,[],[f2838,f961])).
% 2.91/0.74  fof(f961,plain,(
% 2.91/0.74    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.91/0.74    inference(forward_demodulation,[],[f955,f775])).
% 2.91/0.74  fof(f775,plain,(
% 2.91/0.74    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f43,f53])).
% 2.91/0.74  fof(f53,plain,(
% 2.91/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f22])).
% 2.91/0.74  fof(f22,plain,(
% 2.91/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.74    inference(ennf_transformation,[],[f10])).
% 2.91/0.74  fof(f10,axiom,(
% 2.91/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.91/0.74  fof(f955,plain,(
% 2.91/0.74    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f43,f54])).
% 2.91/0.74  fof(f54,plain,(
% 2.91/0.74    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f23])).
% 2.91/0.74  fof(f23,plain,(
% 2.91/0.74    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.74    inference(ennf_transformation,[],[f13])).
% 2.91/0.74  fof(f13,axiom,(
% 2.91/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.91/0.74  fof(f2838,plain,(
% 2.91/0.74    ( ! [X0] : (k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f786,f53])).
% 2.91/0.74  fof(f786,plain,(
% 2.91/0.74    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(backward_demodulation,[],[f410,f775])).
% 2.91/0.74  fof(f410,plain,(
% 2.91/0.74    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f43,f52])).
% 2.91/0.74  fof(f52,plain,(
% 2.91/0.74    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f21])).
% 2.91/0.74  fof(f21,plain,(
% 2.91/0.74    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.74    inference(ennf_transformation,[],[f11])).
% 2.91/0.74  fof(f11,axiom,(
% 2.91/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.91/0.74  fof(f3635,plain,(
% 2.91/0.74    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))))) | spl5_318),
% 2.91/0.74    inference(avatar_component_clause,[],[f3633])).
% 2.91/0.74  fof(f3633,plain,(
% 2.91/0.74    spl5_318 <=> sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)))))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_318])])).
% 2.91/0.74  fof(f3636,plain,(
% 2.91/0.74    ~spl5_318 | ~spl5_6 | spl5_296),
% 2.91/0.74    inference(avatar_split_clause,[],[f3631,f3347,f212,f3633])).
% 2.91/0.74  fof(f212,plain,(
% 2.91/0.74    spl5_6 <=> r1_tarski(sK3,sK1)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.91/0.74  fof(f3347,plain,(
% 2.91/0.74    spl5_296 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_296])])).
% 2.91/0.74  fof(f3631,plain,(
% 2.91/0.74    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3))))) | (~spl5_6 | spl5_296)),
% 2.91/0.74    inference(forward_demodulation,[],[f3588,f61])).
% 2.91/0.74  fof(f61,plain,(
% 2.91/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f5])).
% 2.91/0.74  fof(f5,axiom,(
% 2.91/0.74    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.91/0.74  fof(f3588,plain,(
% 2.91/0.74    ~sP0(sK1,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK3)))) | (~spl5_6 | spl5_296)),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f3349,f2192,f55])).
% 2.91/0.74  fof(f2192,plain,(
% 2.91/0.74    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK1,k4_xboole_0(X0,sK3))))) ) | ~spl5_6),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f65,f2100,f56])).
% 2.91/0.74  fof(f56,plain,(
% 2.91/0.74    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X3,X0) | r2_hidden(X3,X1)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f37])).
% 2.91/0.74  fof(f2100,plain,(
% 2.91/0.74    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(X0,sK3)))) ) | ~spl5_6),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f476,f63])).
% 2.91/0.74  fof(f63,plain,(
% 2.91/0.74    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f25])).
% 2.91/0.74  fof(f25,plain,(
% 2.91/0.74    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.91/0.74    inference(ennf_transformation,[],[f6])).
% 2.91/0.74  fof(f6,axiom,(
% 2.91/0.74    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.91/0.74  fof(f476,plain,(
% 2.91/0.74    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK3))) ) | ~spl5_6),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f214,f62])).
% 2.91/0.74  fof(f62,plain,(
% 2.91/0.74    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f24])).
% 2.91/0.74  fof(f24,plain,(
% 2.91/0.74    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.91/0.74    inference(ennf_transformation,[],[f3])).
% 2.91/0.74  fof(f3,axiom,(
% 2.91/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 2.91/0.74  fof(f214,plain,(
% 2.91/0.74    r1_tarski(sK3,sK1) | ~spl5_6),
% 2.91/0.74    inference(avatar_component_clause,[],[f212])).
% 2.91/0.74  fof(f3349,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1) | spl5_296),
% 2.91/0.74    inference(avatar_component_clause,[],[f3347])).
% 2.91/0.74  fof(f3350,plain,(
% 2.91/0.74    ~spl5_296 | ~spl5_14 | spl5_214),
% 2.91/0.74    inference(avatar_split_clause,[],[f3341,f1975,f262,f3347])).
% 2.91/0.74  fof(f262,plain,(
% 2.91/0.74    spl5_14 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.91/0.74  fof(f1975,plain,(
% 2.91/0.74    spl5_214 <=> r1_tarski(k2_xboole_0(sK2,sK3),sK1)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).
% 2.91/0.74  fof(f3341,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1) | (~spl5_14 | spl5_214)),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f1977,f665])).
% 2.91/0.74  fof(f665,plain,(
% 2.91/0.74    ( ! [X18] : (~r1_tarski(k4_xboole_0(X18,sK2),sK1) | r1_tarski(X18,sK1)) ) | ~spl5_14),
% 2.91/0.74    inference(superposition,[],[f63,f264])).
% 2.91/0.74  fof(f264,plain,(
% 2.91/0.74    sK1 = k2_xboole_0(sK2,sK1) | ~spl5_14),
% 2.91/0.74    inference(avatar_component_clause,[],[f262])).
% 2.91/0.74  fof(f1977,plain,(
% 2.91/0.74    ~r1_tarski(k2_xboole_0(sK2,sK3),sK1) | spl5_214),
% 2.91/0.74    inference(avatar_component_clause,[],[f1975])).
% 2.91/0.74  fof(f1978,plain,(
% 2.91/0.74    ~spl5_214 | spl5_201),
% 2.91/0.74    inference(avatar_split_clause,[],[f1961,f1855,f1975])).
% 2.91/0.74  fof(f1855,plain,(
% 2.91/0.74    spl5_201 <=> r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).
% 2.91/0.74  fof(f1961,plain,(
% 2.91/0.74    ~r1_tarski(k2_xboole_0(sK2,sK3),sK1) | spl5_201),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f65,f1857,f56])).
% 2.91/0.74  fof(f1857,plain,(
% 2.91/0.74    ~r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) | spl5_201),
% 2.91/0.74    inference(avatar_component_clause,[],[f1855])).
% 2.91/0.74  fof(f1865,plain,(
% 2.91/0.74    spl5_86 | ~spl5_130),
% 2.91/0.74    inference(avatar_contradiction_clause,[],[f1864])).
% 2.91/0.74  fof(f1864,plain,(
% 2.91/0.74    $false | (spl5_86 | ~spl5_130)),
% 2.91/0.74    inference(subsumption_resolution,[],[f1851,f471])).
% 2.91/0.74  fof(f471,plain,(
% 2.91/0.74    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f44,f62])).
% 2.91/0.74  fof(f44,plain,(
% 2.91/0.74    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f7])).
% 2.91/0.74  fof(f7,axiom,(
% 2.91/0.74    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.91/0.74  fof(f1851,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) | (spl5_86 | ~spl5_130)),
% 2.91/0.74    inference(backward_demodulation,[],[f881,f1433])).
% 2.91/0.74  fof(f1433,plain,(
% 2.91/0.74    k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) | ~spl5_130),
% 2.91/0.74    inference(avatar_component_clause,[],[f1431])).
% 2.91/0.74  fof(f1431,plain,(
% 2.91/0.74    spl5_130 <=> k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).
% 2.91/0.74  fof(f881,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) | spl5_86),
% 2.91/0.74    inference(avatar_component_clause,[],[f879])).
% 2.91/0.74  fof(f879,plain,(
% 2.91/0.74    spl5_86 <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 2.91/0.74  fof(f1858,plain,(
% 2.91/0.74    ~spl5_201 | spl5_109 | ~spl5_130),
% 2.91/0.74    inference(avatar_split_clause,[],[f1848,f1431,f1167,f1855])).
% 2.91/0.74  fof(f1167,plain,(
% 2.91/0.74    spl5_109 <=> r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 2.91/0.74  fof(f1848,plain,(
% 2.91/0.74    ~r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) | (spl5_109 | ~spl5_130)),
% 2.91/0.74    inference(backward_demodulation,[],[f1169,f1433])).
% 2.91/0.74  fof(f1169,plain,(
% 2.91/0.74    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_109),
% 2.91/0.74    inference(avatar_component_clause,[],[f1167])).
% 2.91/0.74  fof(f1434,plain,(
% 2.91/0.74    spl5_130 | ~spl5_2 | ~spl5_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f1359,f77,f72,f1431])).
% 2.91/0.74  fof(f72,plain,(
% 2.91/0.74    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.91/0.74  fof(f77,plain,(
% 2.91/0.74    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.91/0.74  fof(f1359,plain,(
% 2.91/0.74    k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) | (~spl5_2 | ~spl5_3)),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f79,f74,f64])).
% 2.91/0.74  fof(f64,plain,(
% 2.91/0.74    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.91/0.74    inference(cnf_transformation,[],[f27])).
% 2.91/0.74  fof(f27,plain,(
% 2.91/0.74    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.74    inference(flattening,[],[f26])).
% 2.91/0.74  fof(f26,plain,(
% 2.91/0.74    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.91/0.74    inference(ennf_transformation,[],[f14])).
% 2.91/0.74  fof(f14,axiom,(
% 2.91/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.91/0.74  fof(f74,plain,(
% 2.91/0.74    m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.91/0.74    inference(avatar_component_clause,[],[f72])).
% 2.91/0.74  fof(f79,plain,(
% 2.91/0.74    m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.91/0.74    inference(avatar_component_clause,[],[f77])).
% 2.91/0.74  fof(f1172,plain,(
% 2.91/0.74    ~spl5_109 | spl5_77),
% 2.91/0.74    inference(avatar_split_clause,[],[f1171,f813,f1167])).
% 2.91/0.74  fof(f813,plain,(
% 2.91/0.74    spl5_77 <=> m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 2.91/0.74  fof(f1171,plain,(
% 2.91/0.74    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_77),
% 2.91/0.74    inference(subsumption_resolution,[],[f1163,f42])).
% 2.91/0.74  fof(f1163,plain,(
% 2.91/0.74    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_77),
% 2.91/0.74    inference(resolution,[],[f815,f48])).
% 2.91/0.74  fof(f48,plain,(
% 2.91/0.74    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.91/0.74    inference(cnf_transformation,[],[f33])).
% 2.91/0.74  fof(f815,plain,(
% 2.91/0.74    ~m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_77),
% 2.91/0.74    inference(avatar_component_clause,[],[f813])).
% 2.91/0.74  fof(f882,plain,(
% 2.91/0.74    ~spl5_86 | ~spl5_73 | spl5_78),
% 2.91/0.74    inference(avatar_split_clause,[],[f864,f817,f793,f879])).
% 2.91/0.74  fof(f793,plain,(
% 2.91/0.74    spl5_73 <=> k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 2.91/0.74  fof(f817,plain,(
% 2.91/0.74    spl5_78 <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 2.91/0.74  fof(f864,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) | (~spl5_73 | spl5_78)),
% 2.91/0.74    inference(backward_demodulation,[],[f819,f795])).
% 2.91/0.74  fof(f795,plain,(
% 2.91/0.74    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_73),
% 2.91/0.74    inference(avatar_component_clause,[],[f793])).
% 2.91/0.74  fof(f819,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | spl5_78),
% 2.91/0.74    inference(avatar_component_clause,[],[f817])).
% 2.91/0.74  fof(f820,plain,(
% 2.91/0.74    ~spl5_77 | ~spl5_78 | spl5_1),
% 2.91/0.74    inference(avatar_split_clause,[],[f776,f67,f817,f813])).
% 2.91/0.74  fof(f67,plain,(
% 2.91/0.74    spl5_1 <=> r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.91/0.74  fof(f776,plain,(
% 2.91/0.74    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | ~m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_1),
% 2.91/0.74    inference(superposition,[],[f69,f53])).
% 2.91/0.74  fof(f69,plain,(
% 2.91/0.74    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | spl5_1),
% 2.91/0.74    inference(avatar_component_clause,[],[f67])).
% 2.91/0.74  fof(f796,plain,(
% 2.91/0.74    spl5_73 | ~spl5_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f773,f77,f793])).
% 2.91/0.74  fof(f773,plain,(
% 2.91/0.74    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_3),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f79,f53])).
% 2.91/0.74  fof(f265,plain,(
% 2.91/0.74    spl5_14 | ~spl5_7),
% 2.91/0.74    inference(avatar_split_clause,[],[f260,f217,f262])).
% 2.91/0.74  fof(f217,plain,(
% 2.91/0.74    spl5_7 <=> r1_tarski(sK2,sK1)),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.91/0.74  fof(f260,plain,(
% 2.91/0.74    sK1 = k2_xboole_0(sK2,sK1) | ~spl5_7),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f219,f51])).
% 2.91/0.74  fof(f219,plain,(
% 2.91/0.74    r1_tarski(sK2,sK1) | ~spl5_7),
% 2.91/0.74    inference(avatar_component_clause,[],[f217])).
% 2.91/0.74  fof(f220,plain,(
% 2.91/0.74    spl5_7 | ~spl5_4),
% 2.91/0.74    inference(avatar_split_clause,[],[f207,f113,f217])).
% 2.91/0.74  fof(f113,plain,(
% 2.91/0.74    spl5_4 <=> r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.91/0.74  fof(f207,plain,(
% 2.91/0.74    r1_tarski(sK2,sK1) | ~spl5_4),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f115,f65,f55])).
% 2.91/0.74  fof(f115,plain,(
% 2.91/0.74    r2_hidden(sK2,k1_zfmisc_1(sK1)) | ~spl5_4),
% 2.91/0.74    inference(avatar_component_clause,[],[f113])).
% 2.91/0.74  fof(f215,plain,(
% 2.91/0.74    spl5_6 | ~spl5_5),
% 2.91/0.74    inference(avatar_split_clause,[],[f208,f118,f212])).
% 2.91/0.74  fof(f118,plain,(
% 2.91/0.74    spl5_5 <=> r2_hidden(sK3,k1_zfmisc_1(sK1))),
% 2.91/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.91/0.74  fof(f208,plain,(
% 2.91/0.74    r1_tarski(sK3,sK1) | ~spl5_5),
% 2.91/0.74    inference(unit_resulting_resolution,[],[f120,f65,f55])).
% 2.91/0.74  fof(f120,plain,(
% 2.91/0.74    r2_hidden(sK3,k1_zfmisc_1(sK1)) | ~spl5_5),
% 2.91/0.74    inference(avatar_component_clause,[],[f118])).
% 2.91/0.74  fof(f125,plain,(
% 2.91/0.74    spl5_4 | ~spl5_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f124,f77,f113])).
% 2.91/0.74  fof(f124,plain,(
% 2.91/0.74    r2_hidden(sK2,k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.91/0.74    inference(subsumption_resolution,[],[f109,f42])).
% 2.91/0.74  fof(f109,plain,(
% 2.91/0.74    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.91/0.74    inference(resolution,[],[f47,f79])).
% 2.91/0.74  fof(f123,plain,(
% 2.91/0.74    spl5_5 | ~spl5_2),
% 2.91/0.74    inference(avatar_split_clause,[],[f122,f72,f118])).
% 2.91/0.74  fof(f122,plain,(
% 2.91/0.74    r2_hidden(sK3,k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.91/0.74    inference(subsumption_resolution,[],[f108,f42])).
% 2.91/0.74  fof(f108,plain,(
% 2.91/0.74    r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.91/0.74    inference(resolution,[],[f47,f74])).
% 2.91/0.74  fof(f80,plain,(
% 2.91/0.74    spl5_3),
% 2.91/0.74    inference(avatar_split_clause,[],[f39,f77])).
% 2.91/0.74  fof(f39,plain,(
% 2.91/0.74    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.91/0.74    inference(cnf_transformation,[],[f32])).
% 2.91/0.74  fof(f32,plain,(
% 2.91/0.74    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.91/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f31,f30])).
% 2.91/0.74  fof(f30,plain,(
% 2.91/0.74    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.91/0.74    introduced(choice_axiom,[])).
% 2.91/0.74  fof(f31,plain,(
% 2.91/0.74    ? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 2.91/0.74    introduced(choice_axiom,[])).
% 2.91/0.74  fof(f18,plain,(
% 2.91/0.74    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.91/0.74    inference(ennf_transformation,[],[f17])).
% 2.91/0.74  fof(f17,negated_conjecture,(
% 2.91/0.74    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.91/0.74    inference(negated_conjecture,[],[f16])).
% 2.91/0.74  fof(f16,conjecture,(
% 2.91/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.91/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 2.91/0.74  fof(f75,plain,(
% 2.91/0.74    spl5_2),
% 2.91/0.74    inference(avatar_split_clause,[],[f40,f72])).
% 2.91/0.74  fof(f40,plain,(
% 2.91/0.74    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.91/0.74    inference(cnf_transformation,[],[f32])).
% 2.91/0.74  fof(f70,plain,(
% 2.91/0.74    ~spl5_1),
% 2.91/0.74    inference(avatar_split_clause,[],[f41,f67])).
% 2.91/0.74  fof(f41,plain,(
% 2.91/0.74    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.91/0.74    inference(cnf_transformation,[],[f32])).
% 2.91/0.74  % SZS output end Proof for theBenchmark
% 2.91/0.74  % (24042)------------------------------
% 2.91/0.74  % (24042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.74  % (24042)Termination reason: Refutation
% 2.91/0.74  
% 2.91/0.74  % (24042)Memory used [KB]: 15863
% 2.91/0.74  % (24042)Time elapsed: 0.308 s
% 2.91/0.74  % (24042)------------------------------
% 2.91/0.74  % (24042)------------------------------
% 2.91/0.74  % (24023)Success in time 0.384 s
%------------------------------------------------------------------------------
