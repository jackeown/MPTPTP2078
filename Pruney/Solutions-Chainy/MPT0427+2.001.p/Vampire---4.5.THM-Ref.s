%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 231 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  266 ( 586 expanded)
%              Number of equality atoms :   66 ( 154 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f626,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f213,f290,f465,f495,f534,f539,f545,f554,f585,f622,f625])).

fof(f625,plain,
    ( spl4_27
    | spl4_44 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl4_27
    | spl4_44 ),
    inference(unit_resulting_resolution,[],[f29,f293,f621,f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f621,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl4_44
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f293,plain,
    ( k1_xboole_0 != sK1
    | spl4_27 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl4_27
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f622,plain,
    ( spl4_24
    | ~ spl4_14
    | ~ spl4_44
    | spl4_42 ),
    inference(avatar_split_clause,[],[f617,f582,f619,f153,f278])).

fof(f278,plain,
    ( spl4_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f153,plain,
    ( spl4_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f582,plain,
    ( spl4_42
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f617,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK2
    | spl4_42 ),
    inference(superposition,[],[f584,f274])).

fof(f274,plain,(
    ! [X4,X5] :
      ( k8_setfam_1(X4,X5) = k1_setfam_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
      | k1_xboole_0 = X5 ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X4,X5] :
      ( k8_setfam_1(X4,X5) = k1_setfam_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
      | k1_xboole_0 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4))) ) ),
    inference(superposition,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f584,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f582])).

fof(f585,plain,
    ( spl4_27
    | ~ spl4_18
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f574,f582,f174,f292])).

fof(f174,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f574,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f30,f274])).

fof(f30,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f554,plain,
    ( ~ spl4_24
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl4_24
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f58,f550])).

fof(f550,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_24
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f549,f533])).

fof(f533,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl4_40
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f549,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | ~ spl4_24
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f548,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f548,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_41 ),
    inference(superposition,[],[f30,f538])).

fof(f538,plain,
    ( sK0 = k8_setfam_1(sK0,sK1)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl4_41
  <=> sK0 = k8_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f545,plain,(
    spl4_38 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | spl4_38 ),
    inference(subsumption_resolution,[],[f429,f494])).

fof(f494,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_38 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl4_38
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f429,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f428,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f428,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f413])).

fof(f413,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f539,plain,
    ( ~ spl4_3
    | spl4_41 ),
    inference(avatar_split_clause,[],[f524,f536,f78])).

fof(f78,plain,
    ( spl4_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f524,plain,
    ( sK0 = k8_setfam_1(sK0,sK1)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f119,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k8_setfam_1(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f57,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f534,plain,
    ( spl4_40
    | ~ spl4_38
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f529,f278,f492,f531])).

fof(f529,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f528,f280])).

fof(f528,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ v1_xboole_0(sK2)
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f523,f280])).

fof(f523,plain,
    ( sK0 = k8_setfam_1(sK0,sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f119,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f495,plain,
    ( spl4_3
    | ~ spl4_38
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f490,f278,f492,f78])).

fof(f490,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1)
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f458,f280])).

fof(f458,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f67,f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f465,plain,
    ( ~ spl4_26
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f289,f463])).

fof(f463,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f327,f394])).

fof(f394,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_27 ),
    inference(resolution,[],[f328,f57])).

fof(f328,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_27 ),
    inference(superposition,[],[f31,f294])).

fof(f294,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f292])).

fof(f327,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_27 ),
    inference(superposition,[],[f30,f294])).

fof(f289,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl4_26
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f290,plain,
    ( ~ spl4_14
    | spl4_24
    | spl4_26 ),
    inference(avatar_split_clause,[],[f271,f287,f278,f153])).

fof(f271,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f127,f46])).

fof(f127,plain,(
    r1_tarski(k6_setfam_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f124,f28])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | r1_tarski(k6_setfam_1(X3,X2),X3) ) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f213,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f31,f176])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f192,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f28,f155])).

fof(f155,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:51:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (14092)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (14100)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (14100)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f626,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f192,f213,f290,f465,f495,f534,f539,f545,f554,f585,f622,f625])).
% 0.21/0.51  fof(f625,plain,(
% 0.21/0.51    spl4_27 | spl4_44),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f623])).
% 0.21/0.51  fof(f623,plain,(
% 0.21/0.51    $false | (spl4_27 | spl4_44)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f29,f293,f621,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.51  fof(f621,plain,(
% 0.21/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl4_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f619])).
% 0.21/0.51  fof(f619,plain,(
% 0.21/0.51    spl4_44 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl4_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f292])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl4_27 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.51  fof(f622,plain,(
% 0.21/0.51    spl4_24 | ~spl4_14 | ~spl4_44 | spl4_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f617,f582,f619,f153,f278])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    spl4_24 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl4_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    spl4_42 <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.51  fof(f617,plain,(
% 0.21/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK2 | spl4_42),
% 0.21/0.51    inference(superposition,[],[f584,f274])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k8_setfam_1(X4,X5) = k1_setfam_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4))) | k1_xboole_0 = X5) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f269])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k8_setfam_1(X4,X5) = k1_setfam_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4))) | k1_xboole_0 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))) )),
% 0.21/0.51    inference(superposition,[],[f43,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.51  fof(f584,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | spl4_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f582])).
% 0.21/0.51  fof(f585,plain,(
% 0.21/0.51    spl4_27 | ~spl4_18 | ~spl4_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f574,f582,f174,f292])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl4_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f30,f274])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f554,plain,(
% 0.21/0.51    ~spl4_24 | ~spl4_40 | ~spl4_41),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f551])).
% 0.21/0.51  fof(f551,plain,(
% 0.21/0.51    $false | (~spl4_24 | ~spl4_40 | ~spl4_41)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f58,f550])).
% 0.21/0.51  fof(f550,plain,(
% 0.21/0.51    ~r1_tarski(sK0,sK0) | (~spl4_24 | ~spl4_40 | ~spl4_41)),
% 0.21/0.51    inference(forward_demodulation,[],[f549,f533])).
% 0.21/0.51  fof(f533,plain,(
% 0.21/0.51    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f531])).
% 0.21/0.51  fof(f531,plain,(
% 0.21/0.51    spl4_40 <=> sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.51  fof(f549,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | (~spl4_24 | ~spl4_41)),
% 0.21/0.51    inference(forward_demodulation,[],[f548,f280])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl4_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f278])).
% 0.21/0.51  fof(f548,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_41),
% 0.21/0.51    inference(superposition,[],[f30,f538])).
% 0.21/0.51  fof(f538,plain,(
% 0.21/0.51    sK0 = k8_setfam_1(sK0,sK1) | ~spl4_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f536])).
% 0.21/0.51  fof(f536,plain,(
% 0.21/0.51    spl4_41 <=> sK0 = k8_setfam_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f545,plain,(
% 0.21/0.51    spl4_38),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f540])).
% 0.21/0.51  fof(f540,plain,(
% 0.21/0.51    $false | spl4_38),
% 0.21/0.51    inference(subsumption_resolution,[],[f429,f494])).
% 0.21/0.51  fof(f494,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | spl4_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f492])).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    spl4_38 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f428,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f413])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(superposition,[],[f55,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0))))) = X1 | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f41,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f40,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f39,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f37,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X0)))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f36,f54])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.51  fof(f539,plain,(
% 0.21/0.51    ~spl4_3 | spl4_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f524,f536,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl4_3 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f524,plain,(
% 0.21/0.51    sK0 = k8_setfam_1(sK0,sK1) | ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f119,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | k8_setfam_1(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(superposition,[],[f57,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(equality_resolution,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f534,plain,(
% 0.21/0.51    spl4_40 | ~spl4_38 | ~spl4_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f529,f278,f492,f531])).
% 0.21/0.51  fof(f529,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_24),
% 0.21/0.51    inference(forward_demodulation,[],[f528,f280])).
% 0.21/0.51  fof(f528,plain,(
% 0.21/0.51    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~v1_xboole_0(sK2) | ~spl4_24),
% 0.21/0.51    inference(forward_demodulation,[],[f523,f280])).
% 0.21/0.51  fof(f523,plain,(
% 0.21/0.51    sK0 = k8_setfam_1(sK0,sK2) | ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(resolution,[],[f119,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    spl4_3 | ~spl4_38 | ~spl4_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f490,f278,f492,f78])).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK1) | ~spl4_24),
% 0.21/0.51    inference(forward_demodulation,[],[f458,f280])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(resolution,[],[f67,f29])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(resolution,[],[f33,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    ~spl4_26 | ~spl4_27),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f464])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    $false | (~spl4_26 | ~spl4_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f289,f463])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_27),
% 0.21/0.51    inference(forward_demodulation,[],[f327,f394])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_27),
% 0.21/0.51    inference(resolution,[],[f328,f57])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_27),
% 0.21/0.51    inference(superposition,[],[f31,f294])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl4_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f292])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl4_27),
% 0.21/0.51    inference(superposition,[],[f30,f294])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f287])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    spl4_26 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ~spl4_14 | spl4_24 | spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f271,f287,f278,f153])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    r1_tarski(k8_setfam_1(sK0,sK2),sK0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.51    inference(superposition,[],[f127,f46])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    r1_tarski(k6_setfam_1(sK0,sK2),sK0)),
% 0.21/0.51    inference(resolution,[],[f124,f28])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) | r1_tarski(k6_setfam_1(X3,X2),X3)) )),
% 0.21/0.51    inference(resolution,[],[f44,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl4_18),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    $false | spl4_18),
% 0.21/0.51    inference(subsumption_resolution,[],[f31,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    spl4_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f188])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    $false | spl4_14),
% 0.21/0.51    inference(subsumption_resolution,[],[f28,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (14100)------------------------------
% 0.21/0.51  % (14100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14100)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (14100)Memory used [KB]: 6524
% 0.21/0.51  % (14100)Time elapsed: 0.085 s
% 0.21/0.51  % (14100)------------------------------
% 0.21/0.51  % (14100)------------------------------
% 0.21/0.51  % (14086)Success in time 0.148 s
%------------------------------------------------------------------------------
