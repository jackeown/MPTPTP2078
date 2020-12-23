%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:15 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 225 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 513 expanded)
%              Number of equality atoms :   21 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f127,f828,f1593])).

fof(f1593,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f1581])).

fof(f1581,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f72,f1301,f1561,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1561,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f63,f359])).

fof(f359,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f89,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f57,f56,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f89,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f85,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f85,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f76,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f76,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f63,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1301,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK0,sK2))
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f110,f1296,f62])).

fof(f1296,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f899,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f899,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | spl6_4 ),
    inference(forward_demodulation,[],[f897,f68])).

fof(f897,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f149,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f149,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f46,f115,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f115,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_4
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f110,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f828,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f305,f814,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f814,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f808,f359])).

fof(f808,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f92,f793,f61])).

fof(f793,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f328,f69])).

fof(f328,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f324,f68])).

fof(f324,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f312,f70])).

fof(f312,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f63,f114,f62])).

fof(f114,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f92,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f81,f73])).

fof(f81,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f39,f50])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f305,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f111,f73])).

fof(f111,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f127,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f84,f113,f109])).

fof(f84,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f78,f80])).

fof(f80,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f78,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f36,f75])).

fof(f75,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f40])).

fof(f36,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f83,f113,f109])).

fof(f83,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f79,f80])).

fof(f79,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f37,f75])).

fof(f37,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29955)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (29945)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (29935)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (29936)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (29932)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (29933)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (29938)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (29937)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (29934)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (29958)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.54  % (29943)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.54  % (29940)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.54  % (29960)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (29941)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.54  % (29942)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.54  % (29952)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.54  % (29949)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.54  % (29931)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.55  % (29959)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.55  % (29950)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.55  % (29948)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.55  % (29957)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.55  % (29959)Refutation not found, incomplete strategy% (29959)------------------------------
% 1.30/0.55  % (29959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (29959)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (29959)Memory used [KB]: 10746
% 1.30/0.55  % (29959)Time elapsed: 0.139 s
% 1.30/0.55  % (29959)------------------------------
% 1.30/0.55  % (29959)------------------------------
% 1.30/0.55  % (29951)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.55  % (29954)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.55  % (29944)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (29941)Refutation not found, incomplete strategy% (29941)------------------------------
% 1.50/0.56  % (29941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (29941)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (29941)Memory used [KB]: 10746
% 1.50/0.56  % (29941)Time elapsed: 0.146 s
% 1.50/0.56  % (29941)------------------------------
% 1.50/0.56  % (29941)------------------------------
% 1.50/0.56  % (29953)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.50/0.56  % (29946)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.56  % (29960)Refutation not found, incomplete strategy% (29960)------------------------------
% 1.50/0.56  % (29960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (29960)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (29960)Memory used [KB]: 1663
% 1.50/0.56  % (29960)Time elapsed: 0.157 s
% 1.50/0.56  % (29960)------------------------------
% 1.50/0.56  % (29960)------------------------------
% 1.50/0.57  % (29956)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.58  % (29947)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.58  % (29939)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.60  % (29947)Refutation not found, incomplete strategy% (29947)------------------------------
% 1.50/0.60  % (29947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (29947)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  
% 1.50/0.60  % (29947)Memory used [KB]: 10746
% 1.50/0.60  % (29947)Time elapsed: 0.167 s
% 1.50/0.60  % (29947)------------------------------
% 1.50/0.60  % (29947)------------------------------
% 2.08/0.64  % (29956)Refutation found. Thanks to Tanya!
% 2.08/0.64  % SZS status Theorem for theBenchmark
% 2.08/0.64  % SZS output start Proof for theBenchmark
% 2.08/0.64  fof(f1595,plain,(
% 2.08/0.64    $false),
% 2.08/0.64    inference(avatar_sat_refutation,[],[f116,f127,f828,f1593])).
% 2.08/0.64  fof(f1593,plain,(
% 2.08/0.64    ~spl6_3 | spl6_4),
% 2.08/0.64    inference(avatar_contradiction_clause,[],[f1581])).
% 2.08/0.64  fof(f1581,plain,(
% 2.08/0.64    $false | (~spl6_3 | spl6_4)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f72,f1301,f1561,f62])).
% 2.08/0.64  fof(f62,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f35])).
% 2.08/0.64  fof(f35,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.64    inference(flattening,[],[f34])).
% 2.08/0.64  fof(f34,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.64    inference(ennf_transformation,[],[f14])).
% 2.08/0.64  fof(f14,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.08/0.64  fof(f1561,plain,(
% 2.08/0.64    r1_xboole_0(sK2,k4_xboole_0(sK0,sK2))),
% 2.08/0.64    inference(superposition,[],[f63,f359])).
% 2.08/0.64  fof(f359,plain,(
% 2.08/0.64    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.08/0.64    inference(superposition,[],[f89,f68])).
% 2.08/0.64  fof(f68,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.08/0.64    inference(definition_unfolding,[],[f57,f56,f56])).
% 2.08/0.64  fof(f56,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f12])).
% 2.08/0.64  fof(f12,axiom,(
% 2.08/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.08/0.64  fof(f57,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f2])).
% 2.08/0.64  fof(f2,axiom,(
% 2.08/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.08/0.64  fof(f89,plain,(
% 2.08/0.64    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f85,f67])).
% 2.08/0.64  fof(f67,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f45,f56])).
% 2.08/0.64  fof(f45,plain,(
% 2.08/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.08/0.64    inference(cnf_transformation,[],[f28])).
% 2.08/0.64  fof(f28,plain,(
% 2.08/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.08/0.64    inference(ennf_transformation,[],[f9])).
% 2.08/0.64  fof(f9,axiom,(
% 2.08/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.08/0.64  fof(f85,plain,(
% 2.08/0.64    r1_tarski(sK2,sK0)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f76,f73])).
% 2.08/0.64  fof(f73,plain,(
% 2.08/0.64    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.08/0.64    inference(equality_resolution,[],[f52])).
% 2.08/0.64  fof(f52,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.08/0.64    inference(cnf_transformation,[],[f18])).
% 2.08/0.64  fof(f18,axiom,(
% 2.08/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.08/0.64  fof(f76,plain,(
% 2.08/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f55,f38,f50])).
% 2.08/0.64  fof(f50,plain,(
% 2.08/0.64    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f29])).
% 2.08/0.64  fof(f29,plain,(
% 2.08/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.08/0.64    inference(ennf_transformation,[],[f19])).
% 2.08/0.64  fof(f19,axiom,(
% 2.08/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.08/0.64  fof(f38,plain,(
% 2.08/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.08/0.64    inference(cnf_transformation,[],[f25])).
% 2.08/0.64  fof(f25,plain,(
% 2.08/0.64    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.64    inference(ennf_transformation,[],[f23])).
% 2.08/0.64  fof(f23,negated_conjecture,(
% 2.08/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.08/0.64    inference(negated_conjecture,[],[f22])).
% 2.08/0.64  fof(f22,conjecture,(
% 2.08/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 2.08/0.64  fof(f55,plain,(
% 2.08/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f21])).
% 2.08/0.64  fof(f21,axiom,(
% 2.08/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.08/0.64  fof(f63,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f15])).
% 2.08/0.64  fof(f15,axiom,(
% 2.08/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.08/0.64  fof(f1301,plain,(
% 2.08/0.64    ~r1_xboole_0(sK2,k4_xboole_0(sK0,sK2)) | (~spl6_3 | spl6_4)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f110,f1296,f62])).
% 2.08/0.64  fof(f1296,plain,(
% 2.08/0.64    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f899,f70])).
% 2.08/0.64  fof(f70,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.08/0.64    inference(definition_unfolding,[],[f58,f56])).
% 2.08/0.64  fof(f58,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f30])).
% 2.08/0.64  fof(f30,plain,(
% 2.08/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.08/0.64    inference(ennf_transformation,[],[f24])).
% 2.08/0.64  fof(f24,plain,(
% 2.08/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.08/0.64    inference(rectify,[],[f3])).
% 2.08/0.64  fof(f3,axiom,(
% 2.08/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.08/0.64  fof(f899,plain,(
% 2.08/0.64    r2_hidden(sK4(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) | spl6_4),
% 2.08/0.64    inference(forward_demodulation,[],[f897,f68])).
% 2.08/0.64  fof(f897,plain,(
% 2.08/0.64    r2_hidden(sK4(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) | spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f149,f69])).
% 2.08/0.64  fof(f69,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.08/0.64    inference(definition_unfolding,[],[f59,f56])).
% 2.08/0.64  fof(f59,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f30])).
% 2.08/0.64  fof(f149,plain,(
% 2.08/0.64    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f46,f115,f61])).
% 2.08/0.64  fof(f61,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f33])).
% 2.08/0.64  fof(f33,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.64    inference(flattening,[],[f32])).
% 2.08/0.64  fof(f32,plain,(
% 2.08/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.64    inference(ennf_transformation,[],[f16])).
% 2.08/0.64  fof(f16,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.08/0.64  fof(f115,plain,(
% 2.08/0.64    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl6_4),
% 2.08/0.64    inference(avatar_component_clause,[],[f113])).
% 2.08/0.64  fof(f113,plain,(
% 2.08/0.64    spl6_4 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 2.08/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.08/0.64  fof(f46,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f10])).
% 2.08/0.64  fof(f10,axiom,(
% 2.08/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.08/0.64  fof(f110,plain,(
% 2.08/0.64    r1_tarski(sK1,sK2) | ~spl6_3),
% 2.08/0.64    inference(avatar_component_clause,[],[f109])).
% 2.08/0.64  fof(f109,plain,(
% 2.08/0.64    spl6_3 <=> r1_tarski(sK1,sK2)),
% 2.08/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.08/0.64  fof(f72,plain,(
% 2.08/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.08/0.64    inference(equality_resolution,[],[f42])).
% 2.08/0.64  fof(f42,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.08/0.64    inference(cnf_transformation,[],[f5])).
% 2.08/0.64  fof(f5,axiom,(
% 2.08/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.08/0.64  fof(f828,plain,(
% 2.08/0.64    spl6_3 | ~spl6_4),
% 2.08/0.64    inference(avatar_contradiction_clause,[],[f823])).
% 2.08/0.64  fof(f823,plain,(
% 2.08/0.64    $false | (spl6_3 | ~spl6_4)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f305,f814,f74])).
% 2.08/0.64  fof(f74,plain,(
% 2.08/0.64    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.08/0.64    inference(equality_resolution,[],[f51])).
% 2.08/0.64  fof(f51,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.08/0.64    inference(cnf_transformation,[],[f18])).
% 2.08/0.64  fof(f814,plain,(
% 2.08/0.64    r1_tarski(sK1,sK2) | ~spl6_4),
% 2.08/0.64    inference(forward_demodulation,[],[f808,f359])).
% 2.08/0.64  fof(f808,plain,(
% 2.08/0.64    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | ~spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f92,f793,f61])).
% 2.08/0.64  fof(f793,plain,(
% 2.08/0.64    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f328,f69])).
% 2.08/0.64  fof(f328,plain,(
% 2.08/0.64    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) ) | ~spl6_4),
% 2.08/0.64    inference(forward_demodulation,[],[f324,f68])).
% 2.08/0.64  fof(f324,plain,(
% 2.08/0.64    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)))) ) | ~spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f312,f70])).
% 2.08/0.64  fof(f312,plain,(
% 2.08/0.64    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl6_4),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f63,f114,f62])).
% 2.08/0.64  fof(f114,plain,(
% 2.08/0.64    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl6_4),
% 2.08/0.64    inference(avatar_component_clause,[],[f113])).
% 2.08/0.64  fof(f92,plain,(
% 2.08/0.64    r1_tarski(sK1,sK0)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f81,f73])).
% 2.08/0.64  fof(f81,plain,(
% 2.08/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f55,f39,f50])).
% 2.08/0.64  fof(f39,plain,(
% 2.08/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.08/0.64    inference(cnf_transformation,[],[f25])).
% 2.08/0.64  fof(f305,plain,(
% 2.08/0.64    ~r2_hidden(sK1,k1_zfmisc_1(sK2)) | spl6_3),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f111,f73])).
% 2.08/0.64  fof(f111,plain,(
% 2.08/0.64    ~r1_tarski(sK1,sK2) | spl6_3),
% 2.08/0.64    inference(avatar_component_clause,[],[f109])).
% 2.08/0.64  fof(f127,plain,(
% 2.08/0.64    spl6_3 | spl6_4),
% 2.08/0.64    inference(avatar_split_clause,[],[f84,f113,f109])).
% 2.08/0.64  fof(f84,plain,(
% 2.08/0.64    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.08/0.64    inference(backward_demodulation,[],[f78,f80])).
% 2.08/0.64  fof(f80,plain,(
% 2.08/0.64    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f39,f40])).
% 2.08/0.64  fof(f40,plain,(
% 2.08/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f26])).
% 2.08/0.64  fof(f26,plain,(
% 2.08/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.64    inference(ennf_transformation,[],[f20])).
% 2.08/0.64  fof(f20,axiom,(
% 2.08/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.08/0.64  fof(f78,plain,(
% 2.08/0.64    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.08/0.64    inference(backward_demodulation,[],[f36,f75])).
% 2.08/0.64  fof(f75,plain,(
% 2.08/0.64    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f38,f40])).
% 2.08/0.64  fof(f36,plain,(
% 2.08/0.64    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.08/0.64    inference(cnf_transformation,[],[f25])).
% 2.08/0.64  fof(f116,plain,(
% 2.08/0.64    ~spl6_3 | ~spl6_4),
% 2.08/0.64    inference(avatar_split_clause,[],[f83,f113,f109])).
% 2.08/0.64  fof(f83,plain,(
% 2.08/0.64    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.08/0.64    inference(backward_demodulation,[],[f79,f80])).
% 2.08/0.64  fof(f79,plain,(
% 2.08/0.64    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.08/0.64    inference(backward_demodulation,[],[f37,f75])).
% 2.08/0.64  fof(f37,plain,(
% 2.08/0.64    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 2.08/0.64    inference(cnf_transformation,[],[f25])).
% 2.08/0.64  % SZS output end Proof for theBenchmark
% 2.08/0.64  % (29956)------------------------------
% 2.08/0.64  % (29956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.64  % (29956)Termination reason: Refutation
% 2.08/0.64  
% 2.08/0.64  % (29956)Memory used [KB]: 6908
% 2.08/0.64  % (29956)Time elapsed: 0.212 s
% 2.08/0.64  % (29956)------------------------------
% 2.08/0.64  % (29956)------------------------------
% 2.08/0.65  % (29929)Success in time 0.279 s
%------------------------------------------------------------------------------
