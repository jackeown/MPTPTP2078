%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:29 EST 2020

% Result     : Theorem 3.84s
% Output     : Refutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 186 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  257 ( 642 expanded)
%              Number of equality atoms :   11 (  50 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3457,f3522,f3648])).

fof(f3648,plain,(
    ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f3647])).

fof(f3647,plain,
    ( $false
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f3646,f126])).

fof(f126,plain,(
    ~ sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f86,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ sQ10_eqProxy(X0,X1)
      | sQ10_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f83])).

fof(f83,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f86,plain,(
    ~ sQ10_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f36,f83])).

fof(f36,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).

fof(f3646,plain,
    ( sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f3645,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3645,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f3624,f1110])).

fof(f1110,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f1106])).

fof(f1106,plain,
    ( r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f212,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f212,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK3(X9,sK2),sK1)
      | r1_xboole_0(X9,sK2) ) ),
    inference(resolution,[],[f136,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f136,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f135,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f37,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f135,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f133,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f133,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f34,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3624,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1)
    | ~ spl11_16 ),
    inference(resolution,[],[f361,f458])).

fof(f458,plain,(
    ! [X5] :
      ( ~ r1_tarski(k3_subset_1(sK0,X5),sK1)
      | ~ r1_xboole_0(sK1,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | sQ10_eqProxy(k3_subset_1(sK0,X5),sK1) ) ),
    inference(resolution,[],[f116,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | sQ10_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f60,f83])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f116,plain,(
    ! [X3] :
      ( r1_tarski(sK1,k3_subset_1(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r1_xboole_0(sK1,X3) ) ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f361,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl11_16
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f3522,plain,
    ( ~ spl11_2
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f3521])).

fof(f3521,plain,
    ( $false
    | ~ spl11_2
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1332,f3503])).

fof(f3503,plain,
    ( v1_xboole_0(k3_subset_1(sK0,sK2))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f168,f143])).

fof(f143,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_2
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f168,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f101,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1332,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK0,sK2))
    | spl11_16 ),
    inference(resolution,[],[f369,f74])).

fof(f369,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK2))
    | spl11_16 ),
    inference(resolution,[],[f362,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f362,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | spl11_16 ),
    inference(avatar_component_clause,[],[f360])).

fof(f3457,plain,
    ( spl11_2
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f3441])).

fof(f3441,plain,
    ( $false
    | spl11_2
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f403,f369,f1762,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1762,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2)
    | spl11_2
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1761,f512])).

fof(f512,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | spl11_2 ),
    inference(resolution,[],[f170,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f170,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl11_2 ),
    inference(subsumption_resolution,[],[f169,f144])).

fof(f144,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f169,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f101,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1761,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1747,f370])).

fof(f370,plain,
    ( ~ r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1)
    | spl11_16 ),
    inference(resolution,[],[f362,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1747,plain,
    ( r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2)
    | r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | spl11_16 ),
    inference(resolution,[],[f348,f369])).

fof(f348,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1)
      | ~ r1_tarski(X5,sK0) ) ),
    inference(resolution,[],[f131,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f131,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f129,f74])).

fof(f129,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f33,f45])).

fof(f33,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f403,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f396,f101])).

fof(f396,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f104,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k3_subset_1(sK0,sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | r1_xboole_0(X2,sK2) ) ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (17980)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (17987)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  % (17979)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (17988)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.59  % (17996)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (17995)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.60  % (17976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.86/0.61  % (17977)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.86/0.61  % (17974)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.86/0.62  % (18000)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.86/0.62  % (17975)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.86/0.62  % (17984)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.86/0.63  % (17990)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.03/0.63  % (17991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.03/0.63  % (17993)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.03/0.63  % (17982)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.03/0.63  % (17999)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.03/0.63  % (17998)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.03/0.63  % (17972)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.03/0.63  % (17981)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.03/0.64  % (17997)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.03/0.64  % (17989)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.03/0.64  % (17992)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.03/0.64  % (17983)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.03/0.64  % (17985)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.03/0.64  % (17986)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.03/0.64  % (17989)Refutation not found, incomplete strategy% (17989)------------------------------
% 2.03/0.64  % (17989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.64  % (17989)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.64  
% 2.03/0.64  % (17989)Memory used [KB]: 10618
% 2.03/0.64  % (17989)Time elapsed: 0.143 s
% 2.03/0.64  % (17989)------------------------------
% 2.03/0.64  % (17989)------------------------------
% 2.03/0.64  % (17973)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.03/0.64  % (17994)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.03/0.65  % (18001)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.24/0.66  % (17978)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.76/0.75  % (18005)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.60/0.86  % (17977)Time limit reached!
% 3.60/0.86  % (17977)------------------------------
% 3.60/0.86  % (17977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.86  % (17977)Termination reason: Time limit
% 3.60/0.86  
% 3.60/0.86  % (17977)Memory used [KB]: 7675
% 3.60/0.86  % (17977)Time elapsed: 0.420 s
% 3.60/0.86  % (17977)------------------------------
% 3.60/0.86  % (17977)------------------------------
% 3.84/0.89  % (17985)Refutation found. Thanks to Tanya!
% 3.84/0.89  % SZS status Theorem for theBenchmark
% 3.84/0.89  % SZS output start Proof for theBenchmark
% 3.84/0.89  fof(f3651,plain,(
% 3.84/0.89    $false),
% 3.84/0.89    inference(avatar_sat_refutation,[],[f3457,f3522,f3648])).
% 3.84/0.89  fof(f3648,plain,(
% 3.84/0.89    ~spl11_16),
% 3.84/0.89    inference(avatar_contradiction_clause,[],[f3647])).
% 3.84/0.89  fof(f3647,plain,(
% 3.84/0.89    $false | ~spl11_16),
% 3.84/0.89    inference(subsumption_resolution,[],[f3646,f126])).
% 3.84/0.89  fof(f126,plain,(
% 3.84/0.89    ~sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1)),
% 3.84/0.89    inference(resolution,[],[f86,f99])).
% 3.84/0.89  fof(f99,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~sQ10_eqProxy(X0,X1) | sQ10_eqProxy(X1,X0)) )),
% 3.84/0.89    inference(equality_proxy_axiom,[],[f83])).
% 3.84/0.89  fof(f83,plain,(
% 3.84/0.89    ! [X1,X0] : (sQ10_eqProxy(X0,X1) <=> X0 = X1)),
% 3.84/0.89    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).
% 3.84/0.89  fof(f86,plain,(
% 3.84/0.89    ~sQ10_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 3.84/0.89    inference(equality_proxy_replacement,[],[f36,f83])).
% 3.84/0.89  fof(f36,plain,(
% 3.84/0.89    sK1 != k3_subset_1(sK0,sK2)),
% 3.84/0.89    inference(cnf_transformation,[],[f22])).
% 3.84/0.89  fof(f22,plain,(
% 3.84/0.89    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.89    inference(flattening,[],[f21])).
% 3.84/0.89  fof(f21,plain,(
% 3.84/0.89    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.89    inference(ennf_transformation,[],[f19])).
% 3.84/0.89  fof(f19,negated_conjecture,(
% 3.84/0.89    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 3.84/0.89    inference(negated_conjecture,[],[f18])).
% 3.84/0.89  fof(f18,conjecture,(
% 3.84/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => ~(r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).
% 3.84/0.89  fof(f3646,plain,(
% 3.84/0.89    sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 3.84/0.89    inference(subsumption_resolution,[],[f3645,f35])).
% 3.84/0.89  fof(f35,plain,(
% 3.84/0.89    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.84/0.89    inference(cnf_transformation,[],[f22])).
% 3.84/0.89  fof(f3645,plain,(
% 3.84/0.89    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 3.84/0.89    inference(subsumption_resolution,[],[f3624,f1110])).
% 3.84/0.89  fof(f1110,plain,(
% 3.84/0.89    r1_xboole_0(sK1,sK2)),
% 3.84/0.89    inference(duplicate_literal_removal,[],[f1106])).
% 3.84/0.89  fof(f1106,plain,(
% 3.84/0.89    r1_xboole_0(sK1,sK2) | r1_xboole_0(sK1,sK2)),
% 3.84/0.89    inference(resolution,[],[f212,f48])).
% 3.84/0.89  fof(f48,plain,(
% 3.84/0.89    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f24])).
% 3.84/0.89  fof(f24,plain,(
% 3.84/0.89    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.84/0.89    inference(ennf_transformation,[],[f20])).
% 3.84/0.89  fof(f20,plain,(
% 3.84/0.89    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.84/0.89    inference(rectify,[],[f2])).
% 3.84/0.89  fof(f2,axiom,(
% 3.84/0.89    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.84/0.89  fof(f212,plain,(
% 3.84/0.89    ( ! [X9] : (~r2_hidden(sK3(X9,sK2),sK1) | r1_xboole_0(X9,sK2)) )),
% 3.84/0.89    inference(resolution,[],[f136,f49])).
% 3.84/0.89  fof(f49,plain,(
% 3.84/0.89    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f24])).
% 3.84/0.89  fof(f136,plain,(
% 3.84/0.89    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 3.84/0.89    inference(subsumption_resolution,[],[f135,f113])).
% 3.84/0.89  fof(f113,plain,(
% 3.84/0.89    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 3.84/0.89    inference(resolution,[],[f37,f55])).
% 3.84/0.89  fof(f55,plain,(
% 3.84/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f29])).
% 3.84/0.89  fof(f29,plain,(
% 3.84/0.89    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.89    inference(ennf_transformation,[],[f13])).
% 3.84/0.89  fof(f13,axiom,(
% 3.84/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 3.84/0.89  fof(f37,plain,(
% 3.84/0.89    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.84/0.89    inference(cnf_transformation,[],[f22])).
% 3.84/0.89  fof(f135,plain,(
% 3.84/0.89    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 3.84/0.89    inference(subsumption_resolution,[],[f133,f74])).
% 3.84/0.89  fof(f74,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f32])).
% 3.84/0.89  fof(f32,plain,(
% 3.84/0.89    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 3.84/0.89    inference(ennf_transformation,[],[f4])).
% 3.84/0.89  fof(f4,axiom,(
% 3.84/0.89    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 3.84/0.89  fof(f133,plain,(
% 3.84/0.89    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 3.84/0.89    inference(resolution,[],[f34,f45])).
% 3.84/0.89  fof(f45,plain,(
% 3.84/0.89    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f23])).
% 3.84/0.89  fof(f23,plain,(
% 3.84/0.89    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.84/0.89    inference(ennf_transformation,[],[f8])).
% 3.84/0.89  fof(f8,axiom,(
% 3.84/0.89    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.84/0.89  fof(f34,plain,(
% 3.84/0.89    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f22])).
% 3.84/0.89  fof(f3624,plain,(
% 3.84/0.89    ~r1_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 3.84/0.89    inference(resolution,[],[f361,f458])).
% 3.84/0.89  fof(f458,plain,(
% 3.84/0.89    ( ! [X5] : (~r1_tarski(k3_subset_1(sK0,X5),sK1) | ~r1_xboole_0(sK1,X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | sQ10_eqProxy(k3_subset_1(sK0,X5),sK1)) )),
% 3.84/0.89    inference(resolution,[],[f116,f92])).
% 3.84/0.89  fof(f92,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | sQ10_eqProxy(X0,X1)) )),
% 3.84/0.89    inference(equality_proxy_replacement,[],[f60,f83])).
% 3.84/0.89  fof(f60,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.84/0.89    inference(cnf_transformation,[],[f3])).
% 3.84/0.89  fof(f3,axiom,(
% 3.84/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.84/0.89  fof(f116,plain,(
% 3.84/0.89    ( ! [X3] : (r1_tarski(sK1,k3_subset_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,X3)) )),
% 3.84/0.89    inference(resolution,[],[f37,f57])).
% 3.84/0.89  fof(f57,plain,(
% 3.84/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f30])).
% 3.84/0.89  fof(f30,plain,(
% 3.84/0.89    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.89    inference(ennf_transformation,[],[f16])).
% 3.84/0.89  fof(f16,axiom,(
% 3.84/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 3.84/0.89  fof(f361,plain,(
% 3.84/0.89    r1_tarski(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 3.84/0.89    inference(avatar_component_clause,[],[f360])).
% 3.84/0.89  fof(f360,plain,(
% 3.84/0.89    spl11_16 <=> r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 3.84/0.89    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 3.84/0.89  fof(f3522,plain,(
% 3.84/0.89    ~spl11_2 | spl11_16),
% 3.84/0.89    inference(avatar_contradiction_clause,[],[f3521])).
% 3.84/0.89  fof(f3521,plain,(
% 3.84/0.89    $false | (~spl11_2 | spl11_16)),
% 3.84/0.89    inference(subsumption_resolution,[],[f1332,f3503])).
% 3.84/0.89  fof(f3503,plain,(
% 3.84/0.89    v1_xboole_0(k3_subset_1(sK0,sK2)) | ~spl11_2),
% 3.84/0.89    inference(subsumption_resolution,[],[f168,f143])).
% 3.84/0.89  fof(f143,plain,(
% 3.84/0.89    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl11_2),
% 3.84/0.89    inference(avatar_component_clause,[],[f142])).
% 3.84/0.89  fof(f142,plain,(
% 3.84/0.89    spl11_2 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.84/0.89    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 3.84/0.89  fof(f168,plain,(
% 3.84/0.89    ~v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(k3_subset_1(sK0,sK2))),
% 3.84/0.89    inference(resolution,[],[f101,f44])).
% 3.84/0.89  fof(f44,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f23])).
% 3.84/0.89  fof(f101,plain,(
% 3.84/0.89    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 3.84/0.89    inference(resolution,[],[f35,f50])).
% 3.84/0.89  fof(f50,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.84/0.89    inference(cnf_transformation,[],[f25])).
% 3.84/0.89  fof(f25,plain,(
% 3.84/0.89    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.89    inference(ennf_transformation,[],[f12])).
% 3.84/0.89  fof(f12,axiom,(
% 3.84/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.84/0.89  fof(f1332,plain,(
% 3.84/0.89    ~v1_xboole_0(k3_subset_1(sK0,sK2)) | spl11_16),
% 3.84/0.89    inference(resolution,[],[f369,f74])).
% 3.84/0.89  fof(f369,plain,(
% 3.84/0.89    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK2)) | spl11_16),
% 3.84/0.89    inference(resolution,[],[f362,f62])).
% 3.84/0.89  fof(f62,plain,(
% 3.84/0.89    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f31])).
% 3.84/0.89  fof(f31,plain,(
% 3.84/0.89    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.84/0.89    inference(ennf_transformation,[],[f1])).
% 3.84/0.89  fof(f1,axiom,(
% 3.84/0.89    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.84/0.89  fof(f362,plain,(
% 3.84/0.89    ~r1_tarski(k3_subset_1(sK0,sK2),sK1) | spl11_16),
% 3.84/0.89    inference(avatar_component_clause,[],[f360])).
% 3.84/0.89  fof(f3457,plain,(
% 3.84/0.89    spl11_2 | spl11_16),
% 3.84/0.89    inference(avatar_contradiction_clause,[],[f3441])).
% 3.84/0.89  fof(f3441,plain,(
% 3.84/0.89    $false | (spl11_2 | spl11_16)),
% 3.84/0.89    inference(unit_resulting_resolution,[],[f403,f369,f1762,f47])).
% 3.84/0.89  fof(f47,plain,(
% 3.84/0.89    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f24])).
% 3.84/0.89  fof(f1762,plain,(
% 3.84/0.89    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2) | (spl11_2 | spl11_16)),
% 3.84/0.89    inference(subsumption_resolution,[],[f1761,f512])).
% 3.84/0.89  fof(f512,plain,(
% 3.84/0.89    r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl11_2),
% 3.84/0.89    inference(resolution,[],[f170,f81])).
% 3.84/0.89  fof(f81,plain,(
% 3.84/0.89    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 3.84/0.89    inference(equality_resolution,[],[f71])).
% 3.84/0.89  fof(f71,plain,(
% 3.84/0.89    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.84/0.89    inference(cnf_transformation,[],[f5])).
% 3.84/0.89  fof(f5,axiom,(
% 3.84/0.89    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.84/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.84/0.89  fof(f170,plain,(
% 3.84/0.89    r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl11_2),
% 3.84/0.89    inference(subsumption_resolution,[],[f169,f144])).
% 3.84/0.89  fof(f144,plain,(
% 3.84/0.89    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl11_2),
% 3.84/0.89    inference(avatar_component_clause,[],[f142])).
% 3.84/0.89  fof(f169,plain,(
% 3.84/0.89    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 3.84/0.89    inference(resolution,[],[f101,f46])).
% 3.84/0.89  fof(f46,plain,(
% 3.84/0.89    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f23])).
% 3.84/0.89  fof(f1761,plain,(
% 3.84/0.89    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl11_16),
% 3.84/0.89    inference(subsumption_resolution,[],[f1747,f370])).
% 3.84/0.89  fof(f370,plain,(
% 3.84/0.89    ~r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1) | spl11_16),
% 3.84/0.89    inference(resolution,[],[f362,f63])).
% 3.84/0.89  fof(f63,plain,(
% 3.84/0.89    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f31])).
% 3.84/0.89  fof(f1747,plain,(
% 3.84/0.89    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2) | r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1) | ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl11_16),
% 3.84/0.89    inference(resolution,[],[f348,f369])).
% 3.84/0.89  fof(f348,plain,(
% 3.84/0.89    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r2_hidden(X4,sK2) | r2_hidden(X4,sK1) | ~r1_tarski(X5,sK0)) )),
% 3.84/0.89    inference(resolution,[],[f131,f61])).
% 3.84/0.89  fof(f61,plain,(
% 3.84/0.89    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f31])).
% 3.84/0.89  fof(f131,plain,(
% 3.84/0.89    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 3.84/0.89    inference(subsumption_resolution,[],[f129,f74])).
% 3.84/0.89  fof(f129,plain,(
% 3.84/0.89    ( ! [X1] : (r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 3.84/0.89    inference(resolution,[],[f33,f45])).
% 3.84/0.89  fof(f33,plain,(
% 3.84/0.89    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f22])).
% 3.84/0.89  fof(f403,plain,(
% 3.84/0.89    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 3.84/0.89    inference(subsumption_resolution,[],[f396,f101])).
% 3.84/0.89  fof(f396,plain,(
% 3.84/0.89    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 3.84/0.89    inference(resolution,[],[f104,f77])).
% 3.84/0.89  fof(f77,plain,(
% 3.84/0.89    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/0.89    inference(equality_resolution,[],[f58])).
% 3.84/0.89  fof(f58,plain,(
% 3.84/0.89    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/0.89    inference(cnf_transformation,[],[f3])).
% 3.84/0.89  fof(f104,plain,(
% 3.84/0.89    ( ! [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r1_xboole_0(X2,sK2)) )),
% 3.84/0.89    inference(resolution,[],[f35,f56])).
% 3.84/0.89  fof(f56,plain,(
% 3.84/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) )),
% 3.84/0.89    inference(cnf_transformation,[],[f30])).
% 3.84/0.89  % SZS output end Proof for theBenchmark
% 3.84/0.89  % (17985)------------------------------
% 3.84/0.89  % (17985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.89  % (17985)Termination reason: Refutation
% 3.84/0.89  
% 3.84/0.89  % (17985)Memory used [KB]: 7803
% 3.84/0.89  % (17985)Time elapsed: 0.454 s
% 3.84/0.89  % (17985)------------------------------
% 3.84/0.89  % (17985)------------------------------
% 3.84/0.89  % (17971)Success in time 0.521 s
%------------------------------------------------------------------------------
