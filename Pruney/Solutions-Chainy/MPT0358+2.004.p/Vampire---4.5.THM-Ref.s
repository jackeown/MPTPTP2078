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
% DateTime   : Thu Dec  3 12:44:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 157 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  193 ( 360 expanded)
%              Number of equality atoms :   58 ( 132 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f61,f66,f169,f171,f173,f227])).

fof(f227,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_1
    | spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f59,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f190,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f190,plain,
    ( sK1 = k5_xboole_0(sK1,sK1)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f189,f78])).

fof(f78,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f189,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f188,f175])).

fof(f175,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f174,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f174,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f168,f40])).

fof(f168,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl2_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f188,plain,
    ( k3_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)))
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f182,f36])).

fof(f182,plain,
    ( k3_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f129,f175])).

fof(f129,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f128,f36])).

fof(f128,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f127,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f127,plain,(
    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f125,f36])).

fof(f125,plain,(
    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK1),sK0),k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f67,f118])).

fof(f118,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f67,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f173,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f164,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f164,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl2_4
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f171,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f160,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f160,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl2_3
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f169,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f156,f166,f162,f158])).

fof(f156,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f153,f48])).

fof(f48,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f153,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f42,f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f66,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f30,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f63,f48])).

fof(f63,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f55,f58])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f55,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f61,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f47,f57,f53])).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f46,f57,f53])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f29,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:37:47 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.46  % (26622)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (26638)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.47  % (26622)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f228,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f60,f61,f66,f169,f171,f173,f227])).
% 0.19/0.47  fof(f227,plain,(
% 0.19/0.47    ~spl2_1 | spl2_2 | ~spl2_5),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f226])).
% 0.19/0.47  fof(f226,plain,(
% 0.19/0.47    $false | (~spl2_1 | spl2_2 | ~spl2_5)),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f225])).
% 0.19/0.47  fof(f225,plain,(
% 0.19/0.47    k1_xboole_0 != k1_xboole_0 | (~spl2_1 | spl2_2 | ~spl2_5)),
% 0.19/0.47    inference(superposition,[],[f59,f191])).
% 0.19/0.47  fof(f191,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | (~spl2_1 | ~spl2_5)),
% 0.19/0.47    inference(forward_demodulation,[],[f190,f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.47  fof(f190,plain,(
% 0.19/0.47    sK1 = k5_xboole_0(sK1,sK1) | (~spl2_1 | ~spl2_5)),
% 0.19/0.47    inference(forward_demodulation,[],[f189,f78])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl2_1),
% 0.19/0.47    inference(resolution,[],[f40,f54])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl2_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    spl2_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.47  fof(f189,plain,(
% 0.19/0.47    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))) | ~spl2_5),
% 0.19/0.47    inference(forward_demodulation,[],[f188,f175])).
% 0.19/0.47  fof(f175,plain,(
% 0.19/0.47    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_5),
% 0.19/0.47    inference(superposition,[],[f174,f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.47  fof(f174,plain,(
% 0.19/0.47    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_5),
% 0.19/0.47    inference(resolution,[],[f168,f40])).
% 0.19/0.47  fof(f168,plain,(
% 0.19/0.47    r1_tarski(sK1,sK0) | ~spl2_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f166])).
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    spl2_5 <=> r1_tarski(sK1,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    k3_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))) | ~spl2_5),
% 0.19/0.47    inference(forward_demodulation,[],[f182,f36])).
% 0.19/0.47  fof(f182,plain,(
% 0.19/0.47    k3_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(sK0,sK1))) | ~spl2_5),
% 0.19/0.47    inference(backward_demodulation,[],[f129,f175])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),
% 0.19/0.47    inference(forward_demodulation,[],[f128,f36])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1)))),
% 0.19/0.47    inference(resolution,[],[f127,f51])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.19/0.47    inference(definition_unfolding,[],[f43,f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.47    inference(nnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1))),
% 0.19/0.47    inference(forward_demodulation,[],[f125,f36])).
% 0.19/0.47  fof(f125,plain,(
% 0.19/0.47    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK1),sK0),k3_subset_1(sK0,sK1))),
% 0.19/0.47    inference(superposition,[],[f67,f118])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f49,f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(nnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.19/0.47    inference(negated_conjecture,[],[f15])).
% 0.19/0.47  fof(f15,conjecture,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f41,f39])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 0.19/0.47    inference(superposition,[],[f38,f36])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    k1_xboole_0 != sK1 | spl2_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f57])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    spl2_2 <=> k1_xboole_0 = sK1),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.47  fof(f173,plain,(
% 0.19/0.47    spl2_4),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f172])).
% 0.19/0.47  fof(f172,plain,(
% 0.19/0.47    $false | spl2_4),
% 0.19/0.47    inference(resolution,[],[f164,f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.47  fof(f164,plain,(
% 0.19/0.47    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) | spl2_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f162])).
% 0.19/0.47  fof(f162,plain,(
% 0.19/0.47    spl2_4 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.47  fof(f171,plain,(
% 0.19/0.47    spl2_3),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f170])).
% 0.19/0.47  fof(f170,plain,(
% 0.19/0.47    $false | spl2_3),
% 0.19/0.47    inference(resolution,[],[f160,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,axiom,(
% 0.19/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.47  fof(f160,plain,(
% 0.19/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | spl2_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f158])).
% 0.19/0.47  fof(f158,plain,(
% 0.19/0.47    spl2_3 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.47  fof(f169,plain,(
% 0.19/0.47    ~spl2_3 | ~spl2_4 | spl2_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f156,f166,f162,f158])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    r1_tarski(sK1,sK0) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.19/0.47    inference(superposition,[],[f153,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.19/0.47    inference(definition_unfolding,[],[f32,f45])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f35,f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.48  fof(f153,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(sK1,k3_subset_1(sK0,X0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.19/0.48    inference(resolution,[],[f42,f27])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(flattening,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    spl2_1 | ~spl2_2),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f65])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    $false | (spl2_1 | ~spl2_2)),
% 0.19/0.48    inference(resolution,[],[f30,f64])).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ~r1_tarski(k1_xboole_0,sK0) | (spl2_1 | ~spl2_2)),
% 0.19/0.48    inference(forward_demodulation,[],[f63,f48])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (spl2_1 | ~spl2_2)),
% 0.19/0.48    inference(forward_demodulation,[],[f55,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    k1_xboole_0 = sK1 | ~spl2_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f57])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl2_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f53])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    spl2_1 | spl2_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f47,f57,f53])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.48    inference(definition_unfolding,[],[f28,f31])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ~spl2_1 | ~spl2_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f46,f57,f53])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.48    inference(definition_unfolding,[],[f29,f31])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (26622)------------------------------
% 0.19/0.48  % (26622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (26622)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (26622)Memory used [KB]: 6268
% 0.19/0.48  % (26622)Time elapsed: 0.073 s
% 0.19/0.48  % (26622)------------------------------
% 0.19/0.48  % (26622)------------------------------
% 0.19/0.49  % (26609)Success in time 0.147 s
%------------------------------------------------------------------------------
