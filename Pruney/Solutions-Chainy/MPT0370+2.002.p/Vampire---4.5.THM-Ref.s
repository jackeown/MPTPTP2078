%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:28 EST 2020

% Result     : Theorem 4.12s
% Output     : Refutation 4.12s
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
              <=> ~ r2_hidden(X3,X2) )
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
              <=> ~ r2_hidden(X3,X2) )
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
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:40:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.50  % (16461)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (16466)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (16469)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (16482)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (16474)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (16463)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (16459)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (16462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (16460)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (16467)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (16458)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (16479)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (16470)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (16477)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (16475)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (16478)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (16487)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (16486)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.59  % (16471)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (16473)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.59  % (16475)Refutation not found, incomplete strategy% (16475)------------------------------
% 0.21/0.59  % (16475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (16475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (16475)Memory used [KB]: 10618
% 0.21/0.59  % (16475)Time elapsed: 0.164 s
% 0.21/0.59  % (16475)------------------------------
% 0.21/0.59  % (16475)------------------------------
% 0.21/0.59  % (16484)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.60  % (16472)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (16481)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.61  % (16465)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.61  % (16468)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.61  % (16480)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.62  % (16485)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.63  % (16464)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.63  % (16476)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.96/0.64  % (16483)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 3.01/0.81  % (16512)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.01/0.82  % (16463)Time limit reached!
% 3.01/0.82  % (16463)------------------------------
% 3.01/0.82  % (16463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.82  % (16463)Termination reason: Time limit
% 3.01/0.82  
% 3.01/0.82  % (16463)Memory used [KB]: 7547
% 3.01/0.82  % (16463)Time elapsed: 0.408 s
% 3.01/0.82  % (16463)------------------------------
% 3.01/0.82  % (16463)------------------------------
% 4.12/0.90  % (16471)Refutation found. Thanks to Tanya!
% 4.12/0.90  % SZS status Theorem for theBenchmark
% 4.12/0.90  % SZS output start Proof for theBenchmark
% 4.12/0.90  fof(f3651,plain,(
% 4.12/0.90    $false),
% 4.12/0.90    inference(avatar_sat_refutation,[],[f3457,f3522,f3648])).
% 4.12/0.90  fof(f3648,plain,(
% 4.12/0.90    ~spl11_16),
% 4.12/0.90    inference(avatar_contradiction_clause,[],[f3647])).
% 4.12/0.90  fof(f3647,plain,(
% 4.12/0.90    $false | ~spl11_16),
% 4.12/0.90    inference(subsumption_resolution,[],[f3646,f126])).
% 4.12/0.90  fof(f126,plain,(
% 4.12/0.90    ~sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1)),
% 4.12/0.90    inference(resolution,[],[f86,f99])).
% 4.12/0.90  fof(f99,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~sQ10_eqProxy(X0,X1) | sQ10_eqProxy(X1,X0)) )),
% 4.12/0.90    inference(equality_proxy_axiom,[],[f83])).
% 4.12/0.90  fof(f83,plain,(
% 4.12/0.90    ! [X1,X0] : (sQ10_eqProxy(X0,X1) <=> X0 = X1)),
% 4.12/0.90    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).
% 4.12/0.90  fof(f86,plain,(
% 4.12/0.90    ~sQ10_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 4.12/0.90    inference(equality_proxy_replacement,[],[f36,f83])).
% 4.12/0.90  fof(f36,plain,(
% 4.12/0.90    sK1 != k3_subset_1(sK0,sK2)),
% 4.12/0.90    inference(cnf_transformation,[],[f22])).
% 4.12/0.90  fof(f22,plain,(
% 4.12/0.90    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/0.90    inference(flattening,[],[f21])).
% 4.12/0.90  fof(f21,plain,(
% 4.12/0.90    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/0.90    inference(ennf_transformation,[],[f19])).
% 4.12/0.90  fof(f19,negated_conjecture,(
% 4.12/0.90    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 4.12/0.90    inference(negated_conjecture,[],[f18])).
% 4.12/0.90  fof(f18,conjecture,(
% 4.12/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).
% 4.12/0.90  fof(f3646,plain,(
% 4.12/0.90    sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 4.12/0.90    inference(subsumption_resolution,[],[f3645,f35])).
% 4.12/0.90  fof(f35,plain,(
% 4.12/0.90    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.12/0.90    inference(cnf_transformation,[],[f22])).
% 4.12/0.90  fof(f3645,plain,(
% 4.12/0.90    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 4.12/0.90    inference(subsumption_resolution,[],[f3624,f1110])).
% 4.12/0.90  fof(f1110,plain,(
% 4.12/0.90    r1_xboole_0(sK1,sK2)),
% 4.12/0.90    inference(duplicate_literal_removal,[],[f1106])).
% 4.12/0.90  fof(f1106,plain,(
% 4.12/0.90    r1_xboole_0(sK1,sK2) | r1_xboole_0(sK1,sK2)),
% 4.12/0.90    inference(resolution,[],[f212,f48])).
% 4.12/0.90  fof(f48,plain,(
% 4.12/0.90    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f24])).
% 4.12/0.90  fof(f24,plain,(
% 4.12/0.90    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.12/0.90    inference(ennf_transformation,[],[f20])).
% 4.12/0.90  fof(f20,plain,(
% 4.12/0.90    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.12/0.90    inference(rectify,[],[f2])).
% 4.12/0.90  fof(f2,axiom,(
% 4.12/0.90    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.12/0.90  fof(f212,plain,(
% 4.12/0.90    ( ! [X9] : (~r2_hidden(sK3(X9,sK2),sK1) | r1_xboole_0(X9,sK2)) )),
% 4.12/0.90    inference(resolution,[],[f136,f49])).
% 4.12/0.90  fof(f49,plain,(
% 4.12/0.90    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f24])).
% 4.12/0.90  fof(f136,plain,(
% 4.12/0.90    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 4.12/0.90    inference(subsumption_resolution,[],[f135,f113])).
% 4.12/0.90  fof(f113,plain,(
% 4.12/0.90    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 4.12/0.90    inference(resolution,[],[f37,f55])).
% 4.12/0.90  fof(f55,plain,(
% 4.12/0.90    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f29])).
% 4.12/0.90  fof(f29,plain,(
% 4.12/0.90    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/0.90    inference(ennf_transformation,[],[f13])).
% 4.12/0.90  fof(f13,axiom,(
% 4.12/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 4.12/0.90  fof(f37,plain,(
% 4.12/0.90    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.12/0.90    inference(cnf_transformation,[],[f22])).
% 4.12/0.90  fof(f135,plain,(
% 4.12/0.90    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 4.12/0.90    inference(subsumption_resolution,[],[f133,f74])).
% 4.12/0.90  fof(f74,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f32])).
% 4.12/0.90  fof(f32,plain,(
% 4.12/0.90    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 4.12/0.90    inference(ennf_transformation,[],[f4])).
% 4.12/0.90  fof(f4,axiom,(
% 4.12/0.90    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 4.12/0.90  fof(f133,plain,(
% 4.12/0.90    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 4.12/0.90    inference(resolution,[],[f34,f45])).
% 4.12/0.90  fof(f45,plain,(
% 4.12/0.90    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f23])).
% 4.12/0.90  fof(f23,plain,(
% 4.12/0.90    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.12/0.90    inference(ennf_transformation,[],[f8])).
% 4.12/0.90  fof(f8,axiom,(
% 4.12/0.90    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 4.12/0.90  fof(f34,plain,(
% 4.12/0.90    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f22])).
% 4.12/0.90  fof(f3624,plain,(
% 4.12/0.90    ~r1_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sQ10_eqProxy(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 4.12/0.90    inference(resolution,[],[f361,f458])).
% 4.12/0.90  fof(f458,plain,(
% 4.12/0.90    ( ! [X5] : (~r1_tarski(k3_subset_1(sK0,X5),sK1) | ~r1_xboole_0(sK1,X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | sQ10_eqProxy(k3_subset_1(sK0,X5),sK1)) )),
% 4.12/0.90    inference(resolution,[],[f116,f92])).
% 4.12/0.90  fof(f92,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | sQ10_eqProxy(X0,X1)) )),
% 4.12/0.90    inference(equality_proxy_replacement,[],[f60,f83])).
% 4.12/0.90  fof(f60,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 4.12/0.90    inference(cnf_transformation,[],[f3])).
% 4.12/0.90  fof(f3,axiom,(
% 4.12/0.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.12/0.90  fof(f116,plain,(
% 4.12/0.90    ( ! [X3] : (r1_tarski(sK1,k3_subset_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,X3)) )),
% 4.12/0.90    inference(resolution,[],[f37,f57])).
% 4.12/0.90  fof(f57,plain,(
% 4.12/0.90    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f30])).
% 4.12/0.90  fof(f30,plain,(
% 4.12/0.90    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/0.90    inference(ennf_transformation,[],[f16])).
% 4.12/0.90  fof(f16,axiom,(
% 4.12/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 4.12/0.90  fof(f361,plain,(
% 4.12/0.90    r1_tarski(k3_subset_1(sK0,sK2),sK1) | ~spl11_16),
% 4.12/0.90    inference(avatar_component_clause,[],[f360])).
% 4.12/0.90  fof(f360,plain,(
% 4.12/0.90    spl11_16 <=> r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 4.12/0.90    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 4.12/0.90  fof(f3522,plain,(
% 4.12/0.90    ~spl11_2 | spl11_16),
% 4.12/0.90    inference(avatar_contradiction_clause,[],[f3521])).
% 4.12/0.90  fof(f3521,plain,(
% 4.12/0.90    $false | (~spl11_2 | spl11_16)),
% 4.12/0.90    inference(subsumption_resolution,[],[f1332,f3503])).
% 4.12/0.90  fof(f3503,plain,(
% 4.12/0.90    v1_xboole_0(k3_subset_1(sK0,sK2)) | ~spl11_2),
% 4.12/0.90    inference(subsumption_resolution,[],[f168,f143])).
% 4.12/0.90  fof(f143,plain,(
% 4.12/0.90    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl11_2),
% 4.12/0.90    inference(avatar_component_clause,[],[f142])).
% 4.12/0.90  fof(f142,plain,(
% 4.12/0.90    spl11_2 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 4.12/0.90    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 4.12/0.90  fof(f168,plain,(
% 4.12/0.90    ~v1_xboole_0(k1_zfmisc_1(sK0)) | v1_xboole_0(k3_subset_1(sK0,sK2))),
% 4.12/0.90    inference(resolution,[],[f101,f44])).
% 4.12/0.90  fof(f44,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f23])).
% 4.12/0.90  fof(f101,plain,(
% 4.12/0.90    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 4.12/0.90    inference(resolution,[],[f35,f50])).
% 4.12/0.90  fof(f50,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 4.12/0.90    inference(cnf_transformation,[],[f25])).
% 4.12/0.90  fof(f25,plain,(
% 4.12/0.90    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/0.90    inference(ennf_transformation,[],[f12])).
% 4.12/0.90  fof(f12,axiom,(
% 4.12/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.12/0.90  fof(f1332,plain,(
% 4.12/0.90    ~v1_xboole_0(k3_subset_1(sK0,sK2)) | spl11_16),
% 4.12/0.90    inference(resolution,[],[f369,f74])).
% 4.12/0.90  fof(f369,plain,(
% 4.12/0.90    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),k3_subset_1(sK0,sK2)) | spl11_16),
% 4.12/0.90    inference(resolution,[],[f362,f62])).
% 4.12/0.90  fof(f62,plain,(
% 4.12/0.90    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f31])).
% 4.12/0.90  fof(f31,plain,(
% 4.12/0.90    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.12/0.90    inference(ennf_transformation,[],[f1])).
% 4.12/0.90  fof(f1,axiom,(
% 4.12/0.90    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 4.12/0.90  fof(f362,plain,(
% 4.12/0.90    ~r1_tarski(k3_subset_1(sK0,sK2),sK1) | spl11_16),
% 4.12/0.90    inference(avatar_component_clause,[],[f360])).
% 4.12/0.90  fof(f3457,plain,(
% 4.12/0.90    spl11_2 | spl11_16),
% 4.12/0.90    inference(avatar_contradiction_clause,[],[f3441])).
% 4.12/0.90  fof(f3441,plain,(
% 4.12/0.90    $false | (spl11_2 | spl11_16)),
% 4.12/0.90    inference(unit_resulting_resolution,[],[f403,f369,f1762,f47])).
% 4.12/0.90  fof(f47,plain,(
% 4.12/0.90    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f24])).
% 4.12/0.90  fof(f1762,plain,(
% 4.12/0.90    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2) | (spl11_2 | spl11_16)),
% 4.12/0.90    inference(subsumption_resolution,[],[f1761,f512])).
% 4.12/0.90  fof(f512,plain,(
% 4.12/0.90    r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl11_2),
% 4.12/0.90    inference(resolution,[],[f170,f81])).
% 4.12/0.90  fof(f81,plain,(
% 4.12/0.90    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 4.12/0.90    inference(equality_resolution,[],[f71])).
% 4.12/0.90  fof(f71,plain,(
% 4.12/0.90    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.12/0.90    inference(cnf_transformation,[],[f5])).
% 4.12/0.90  fof(f5,axiom,(
% 4.12/0.90    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.12/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 4.12/0.90  fof(f170,plain,(
% 4.12/0.90    r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl11_2),
% 4.12/0.90    inference(subsumption_resolution,[],[f169,f144])).
% 4.12/0.90  fof(f144,plain,(
% 4.12/0.90    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl11_2),
% 4.12/0.90    inference(avatar_component_clause,[],[f142])).
% 4.12/0.90  fof(f169,plain,(
% 4.12/0.90    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 4.12/0.90    inference(resolution,[],[f101,f46])).
% 4.12/0.90  fof(f46,plain,(
% 4.12/0.90    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f23])).
% 4.12/0.90  fof(f1761,plain,(
% 4.12/0.90    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl11_16),
% 4.12/0.90    inference(subsumption_resolution,[],[f1747,f370])).
% 4.12/0.90  fof(f370,plain,(
% 4.12/0.90    ~r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1) | spl11_16),
% 4.12/0.90    inference(resolution,[],[f362,f63])).
% 4.12/0.90  fof(f63,plain,(
% 4.12/0.90    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f31])).
% 4.12/0.90  fof(f1747,plain,(
% 4.12/0.90    r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK2) | r2_hidden(sK5(k3_subset_1(sK0,sK2),sK1),sK1) | ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl11_16),
% 4.12/0.90    inference(resolution,[],[f348,f369])).
% 4.12/0.90  fof(f348,plain,(
% 4.12/0.90    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r2_hidden(X4,sK2) | r2_hidden(X4,sK1) | ~r1_tarski(X5,sK0)) )),
% 4.12/0.90    inference(resolution,[],[f131,f61])).
% 4.12/0.90  fof(f61,plain,(
% 4.12/0.90    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f31])).
% 4.12/0.90  fof(f131,plain,(
% 4.12/0.90    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1) | r2_hidden(X1,sK2)) )),
% 4.12/0.90    inference(subsumption_resolution,[],[f129,f74])).
% 4.12/0.90  fof(f129,plain,(
% 4.12/0.90    ( ! [X1] : (r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 4.12/0.90    inference(resolution,[],[f33,f45])).
% 4.12/0.90  fof(f33,plain,(
% 4.12/0.90    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f22])).
% 4.12/0.90  fof(f403,plain,(
% 4.12/0.90    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 4.12/0.90    inference(subsumption_resolution,[],[f396,f101])).
% 4.12/0.90  fof(f396,plain,(
% 4.12/0.90    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 4.12/0.90    inference(resolution,[],[f104,f77])).
% 4.12/0.90  fof(f77,plain,(
% 4.12/0.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.12/0.90    inference(equality_resolution,[],[f58])).
% 4.12/0.90  fof(f58,plain,(
% 4.12/0.90    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.12/0.90    inference(cnf_transformation,[],[f3])).
% 4.12/0.90  fof(f104,plain,(
% 4.12/0.90    ( ! [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r1_xboole_0(X2,sK2)) )),
% 4.12/0.90    inference(resolution,[],[f35,f56])).
% 4.12/0.90  fof(f56,plain,(
% 4.12/0.90    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) )),
% 4.12/0.90    inference(cnf_transformation,[],[f30])).
% 4.12/0.90  % SZS output end Proof for theBenchmark
% 4.12/0.90  % (16471)------------------------------
% 4.12/0.90  % (16471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.90  % (16471)Termination reason: Refutation
% 4.12/0.90  
% 4.12/0.90  % (16471)Memory used [KB]: 7803
% 4.12/0.90  % (16471)Time elapsed: 0.501 s
% 4.12/0.90  % (16471)------------------------------
% 4.12/0.90  % (16471)------------------------------
% 4.12/0.91  % (16457)Success in time 0.54 s
%------------------------------------------------------------------------------
