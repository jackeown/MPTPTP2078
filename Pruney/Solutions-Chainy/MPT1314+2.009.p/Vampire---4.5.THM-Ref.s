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
% DateTime   : Thu Dec  3 13:13:45 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 262 expanded)
%              Number of leaves         :   27 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  456 (1462 expanded)
%              Number of equality atoms :   60 ( 223 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f429,f432,f538])).

fof(f538,plain,
    ( ~ spl13_6
    | ~ spl13_7 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f536,f60])).

fof(f60,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v3_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v3_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK6)
              & m1_pre_topc(X2,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK6)
            & m1_pre_topc(X2,sK6) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK7 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK7,sK6)
          & m1_pre_topc(X2,sK6) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK7 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK7,sK6)
        & m1_pre_topc(X2,sK6) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK8)
          & sK7 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
      & v3_pre_topc(sK7,sK6)
      & m1_pre_topc(sK8,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK8)
        & sK7 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
   => ( ~ v3_pre_topc(sK9,sK8)
      & sK7 = sK9
      & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f536,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | ~ spl13_6
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f535,f58])).

fof(f58,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f535,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ spl13_6
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f534,f428])).

fof(f428,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl13_7
  <=> r1_tarski(sK9,u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f534,plain,
    ( ~ r1_tarski(sK9,u1_struct_0(sK8))
    | ~ l1_pre_topc(sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f533,f423])).

fof(f423,plain,
    ( l1_struct_0(sK8)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl13_6
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f533,plain,
    ( ~ l1_struct_0(sK8)
    | ~ r1_tarski(sK9,u1_struct_0(sK8))
    | ~ l1_pre_topc(sK6)
    | ~ m1_pre_topc(sK8,sK6) ),
    inference(resolution,[],[f531,f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ sP4(sK9,sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK8,X0) ) ),
    inference(subsumption_resolution,[],[f191,f64])).

fof(f64,plain,(
    ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0)
      | ~ sP4(sK9,sK8,X0)
      | v3_pre_topc(sK9,sK8) ) ),
    inference(resolution,[],[f186,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ sP4(X2,X1,X0)
      | v3_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v3_pre_topc(X2,X1)
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ v3_pre_topc(X2,X1) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v3_pre_topc(X2,X1)
      <=> sP4(X2,X1,X0) )
      | ~ sP5(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f186,plain,(
    ! [X0] :
      ( sP5(X0,sK8,sK9)
      | ~ m1_pre_topc(sK8,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f91,f62])).

fof(f62,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP5(X0,X1,X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP5(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f34,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( sP4(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

fof(f531,plain,(
    ! [X1] :
      ( sP4(sK9,X1,sK6)
      | ~ l1_struct_0(X1)
      | ~ r1_tarski(sK9,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f525,f99])).

fof(f99,plain,(
    v3_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f63,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f525,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(sK9,sK6)
      | sP4(sK9,X1,sK6)
      | ~ l1_struct_0(X1)
      | ~ r1_tarski(sK9,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f402,f100])).

fof(f100,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f40])).

fof(f402,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ v3_pre_topc(X17,X18)
      | sP4(X17,X16,X18)
      | ~ l1_struct_0(X16)
      | ~ r1_tarski(X17,u1_struct_0(X16)) ) ),
    inference(subsumption_resolution,[],[f395,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f66,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f395,plain,(
    ! [X17,X18,X16] :
      ( sP4(X17,X16,X18)
      | ~ v3_pre_topc(X17,X18)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ l1_struct_0(X16)
      | ~ m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X16)))
      | ~ r1_tarski(X17,u1_struct_0(X16)) ) ),
    inference(superposition,[],[f225,f176])).

fof(f176,plain,(
    ! [X6,X4,X5] :
      ( k9_subset_1(X6,X4,X5) = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f102,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f95,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f98,f94])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( sP4(k9_subset_1(u1_struct_0(X0),X1,u1_struct_0(X0)),X0,X2)
      | ~ v3_pre_topc(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f104,f67])).

fof(f67,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f104,plain,(
    ! [X2,X3,X1] :
      ( sP4(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X1),sK12(X0,X1,X2),k2_struct_0(X1)) = X0
          & v3_pre_topc(sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X1),sK12(X0,X1,X2),k2_struct_0(X1)) = X0
        & v3_pre_topc(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( sP4(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP4(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f432,plain,(
    spl13_6 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | spl13_6 ),
    inference(subsumption_resolution,[],[f430,f109])).

fof(f109,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f108,f58])).

fof(f108,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f84,f60])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f430,plain,
    ( ~ l1_pre_topc(sK8)
    | spl13_6 ),
    inference(resolution,[],[f424,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f424,plain,
    ( ~ l1_struct_0(sK8)
    | spl13_6 ),
    inference(avatar_component_clause,[],[f422])).

fof(f429,plain,
    ( ~ spl13_6
    | spl13_7 ),
    inference(avatar_split_clause,[],[f420,f426,f422])).

fof(f420,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8))
    | ~ l1_struct_0(sK8) ),
    inference(superposition,[],[f417,f67])).

fof(f417,plain,(
    r1_tarski(sK9,k2_struct_0(sK8)) ),
    inference(subsumption_resolution,[],[f410,f109])).

fof(f410,plain,
    ( ~ l1_pre_topc(sK8)
    | r1_tarski(sK9,k2_struct_0(sK8)) ),
    inference(resolution,[],[f409,f62])).

fof(f409,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | r1_tarski(X0,k2_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | r1_tarski(X0,k2_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f344,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | r1_tarski(X0,k2_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f334,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f112,f84])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | sP2(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f69,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f31,f30,f29,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & r2_hidden(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> sP0(X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( ! [X2] :
            ( sP1(X0,X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP2(X1,X0) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f334,plain,(
    ! [X4,X2,X3] :
      ( ~ sP2(k1_pre_topc(X2,X3),X4)
      | r1_tarski(X3,k2_struct_0(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f71,f331])).

fof(f331,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f330,f97])).

fof(f330,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f106,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ~ sP1(X1,X0,sK10(X0,X1))
          & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP1(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP1(X1,X0,sK10(X0,X1))
        & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ sP1(X1,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP1(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ~ sP1(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ~ sP1(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (22532)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22532)Refutation not found, incomplete strategy% (22532)------------------------------
% 0.21/0.50  % (22532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22532)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22532)Memory used [KB]: 10746
% 0.21/0.50  % (22532)Time elapsed: 0.085 s
% 0.21/0.50  % (22532)------------------------------
% 0.21/0.50  % (22532)------------------------------
% 0.21/0.50  % (22531)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (22534)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22535)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (22530)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (22548)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (22551)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (22549)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (22556)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (22539)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (22547)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (22555)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (22547)Refutation not found, incomplete strategy% (22547)------------------------------
% 0.21/0.51  % (22547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22533)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (22538)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (22559)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (22547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22547)Memory used [KB]: 10618
% 0.21/0.52  % (22547)Time elapsed: 0.111 s
% 0.21/0.52  % (22547)------------------------------
% 0.21/0.52  % (22547)------------------------------
% 0.21/0.52  % (22558)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (22553)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (22542)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22550)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (22557)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (22539)Refutation not found, incomplete strategy% (22539)------------------------------
% 0.21/0.52  % (22539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22539)Memory used [KB]: 10746
% 0.21/0.52  % (22539)Time elapsed: 0.123 s
% 0.21/0.52  % (22539)------------------------------
% 0.21/0.52  % (22539)------------------------------
% 0.21/0.53  % (22545)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.53  % (22543)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.53  % (22541)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.53  % (22552)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.53  % (22538)Refutation not found, incomplete strategy% (22538)------------------------------
% 1.38/0.53  % (22538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (22544)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.53  % (22538)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (22538)Memory used [KB]: 10874
% 1.38/0.53  % (22538)Time elapsed: 0.127 s
% 1.38/0.53  % (22538)------------------------------
% 1.38/0.53  % (22538)------------------------------
% 1.38/0.53  % (22537)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.54  % (22534)Refutation not found, incomplete strategy% (22534)------------------------------
% 1.38/0.54  % (22534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22534)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22534)Memory used [KB]: 6524
% 1.38/0.54  % (22534)Time elapsed: 0.140 s
% 1.38/0.54  % (22534)------------------------------
% 1.38/0.54  % (22534)------------------------------
% 1.38/0.54  % (22546)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (22536)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (22552)Refutation not found, incomplete strategy% (22552)------------------------------
% 1.38/0.54  % (22552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22552)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22552)Memory used [KB]: 10746
% 1.38/0.54  % (22552)Time elapsed: 0.142 s
% 1.38/0.54  % (22552)------------------------------
% 1.38/0.54  % (22552)------------------------------
% 1.44/0.55  % (22540)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.55  % (22554)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.55  % (22540)Refutation not found, incomplete strategy% (22540)------------------------------
% 1.44/0.55  % (22540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (22540)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (22540)Memory used [KB]: 10746
% 1.44/0.55  % (22540)Time elapsed: 0.142 s
% 1.44/0.55  % (22540)------------------------------
% 1.44/0.55  % (22540)------------------------------
% 1.44/0.57  % (22557)Refutation found. Thanks to Tanya!
% 1.44/0.57  % SZS status Theorem for theBenchmark
% 1.44/0.57  % SZS output start Proof for theBenchmark
% 1.44/0.57  fof(f539,plain,(
% 1.44/0.57    $false),
% 1.44/0.57    inference(avatar_sat_refutation,[],[f429,f432,f538])).
% 1.44/0.57  fof(f538,plain,(
% 1.44/0.57    ~spl13_6 | ~spl13_7),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f537])).
% 1.44/0.57  fof(f537,plain,(
% 1.44/0.57    $false | (~spl13_6 | ~spl13_7)),
% 1.44/0.57    inference(subsumption_resolution,[],[f536,f60])).
% 1.44/0.57  fof(f60,plain,(
% 1.44/0.57    m1_pre_topc(sK8,sK6)),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f40,plain,(
% 1.44/0.57    (((~v3_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f39,f38,f37,f36])).
% 1.44/0.57  fof(f36,plain,(
% 1.44/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f37,plain,(
% 1.44/0.57    ? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f38,plain,(
% 1.44/0.57    ? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(X2,sK6)) => (? [X3] : (~v3_pre_topc(X3,sK8) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f39,plain,(
% 1.44/0.57    ? [X3] : (~v3_pre_topc(X3,sK8) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) => (~v3_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f16,plain,(
% 1.44/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.44/0.57    inference(flattening,[],[f15])).
% 1.44/0.57  fof(f15,plain,(
% 1.44/0.57    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f14])).
% 1.44/0.57  fof(f14,negated_conjecture,(
% 1.44/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.44/0.57    inference(negated_conjecture,[],[f13])).
% 1.44/0.57  fof(f13,conjecture,(
% 1.44/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 1.44/0.57  fof(f536,plain,(
% 1.44/0.57    ~m1_pre_topc(sK8,sK6) | (~spl13_6 | ~spl13_7)),
% 1.44/0.57    inference(subsumption_resolution,[],[f535,f58])).
% 1.44/0.57  fof(f58,plain,(
% 1.44/0.57    l1_pre_topc(sK6)),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f535,plain,(
% 1.44/0.57    ~l1_pre_topc(sK6) | ~m1_pre_topc(sK8,sK6) | (~spl13_6 | ~spl13_7)),
% 1.44/0.57    inference(subsumption_resolution,[],[f534,f428])).
% 1.44/0.57  fof(f428,plain,(
% 1.44/0.57    r1_tarski(sK9,u1_struct_0(sK8)) | ~spl13_7),
% 1.44/0.57    inference(avatar_component_clause,[],[f426])).
% 1.44/0.57  fof(f426,plain,(
% 1.44/0.57    spl13_7 <=> r1_tarski(sK9,u1_struct_0(sK8))),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 1.44/0.57  fof(f534,plain,(
% 1.44/0.57    ~r1_tarski(sK9,u1_struct_0(sK8)) | ~l1_pre_topc(sK6) | ~m1_pre_topc(sK8,sK6) | ~spl13_6),
% 1.44/0.57    inference(subsumption_resolution,[],[f533,f423])).
% 1.44/0.57  fof(f423,plain,(
% 1.44/0.57    l1_struct_0(sK8) | ~spl13_6),
% 1.44/0.57    inference(avatar_component_clause,[],[f422])).
% 1.44/0.57  fof(f422,plain,(
% 1.44/0.57    spl13_6 <=> l1_struct_0(sK8)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 1.44/0.57  fof(f533,plain,(
% 1.44/0.57    ~l1_struct_0(sK8) | ~r1_tarski(sK9,u1_struct_0(sK8)) | ~l1_pre_topc(sK6) | ~m1_pre_topc(sK8,sK6)),
% 1.44/0.57    inference(resolution,[],[f531,f193])).
% 1.44/0.57  fof(f193,plain,(
% 1.44/0.57    ( ! [X0] : (~sP4(sK9,sK8,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK8,X0)) )),
% 1.44/0.57    inference(subsumption_resolution,[],[f191,f64])).
% 1.44/0.57  fof(f64,plain,(
% 1.44/0.57    ~v3_pre_topc(sK9,sK8)),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f191,plain,(
% 1.44/0.57    ( ! [X0] : (~m1_pre_topc(sK8,X0) | ~l1_pre_topc(X0) | ~sP4(sK9,sK8,X0) | v3_pre_topc(sK9,sK8)) )),
% 1.44/0.57    inference(resolution,[],[f186,f86])).
% 1.44/0.57  fof(f86,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | v3_pre_topc(X2,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f52])).
% 1.44/0.57  fof(f52,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (((v3_pre_topc(X2,X1) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~v3_pre_topc(X2,X1))) | ~sP5(X0,X1,X2))),
% 1.44/0.57    inference(nnf_transformation,[],[f34])).
% 1.44/0.57  fof(f34,plain,(
% 1.44/0.57    ! [X0,X1,X2] : ((v3_pre_topc(X2,X1) <=> sP4(X2,X1,X0)) | ~sP5(X0,X1,X2))),
% 1.44/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.44/0.57  fof(f186,plain,(
% 1.44/0.57    ( ! [X0] : (sP5(X0,sK8,sK9) | ~m1_pre_topc(sK8,X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.57    inference(resolution,[],[f91,f62])).
% 1.44/0.57  fof(f62,plain,(
% 1.44/0.57    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f91,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP5(X0,X1,X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f35])).
% 1.44/0.57  fof(f35,plain,(
% 1.44/0.57    ! [X0] : (! [X1] : (! [X2] : (sP5(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.57    inference(definition_folding,[],[f21,f34,f33])).
% 1.44/0.57  fof(f33,plain,(
% 1.44/0.57    ! [X2,X1,X0] : (sP4(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.44/0.57  fof(f21,plain,(
% 1.44/0.57    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f12])).
% 1.44/0.57  fof(f12,axiom,(
% 1.44/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).
% 1.44/0.57  fof(f531,plain,(
% 1.44/0.57    ( ! [X1] : (sP4(sK9,X1,sK6) | ~l1_struct_0(X1) | ~r1_tarski(sK9,u1_struct_0(X1))) )),
% 1.44/0.57    inference(subsumption_resolution,[],[f525,f99])).
% 1.44/0.57  fof(f99,plain,(
% 1.44/0.57    v3_pre_topc(sK9,sK6)),
% 1.44/0.57    inference(definition_unfolding,[],[f61,f63])).
% 1.44/0.57  fof(f63,plain,(
% 1.44/0.57    sK7 = sK9),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f61,plain,(
% 1.44/0.57    v3_pre_topc(sK7,sK6)),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f525,plain,(
% 1.44/0.57    ( ! [X1] : (~v3_pre_topc(sK9,sK6) | sP4(sK9,X1,sK6) | ~l1_struct_0(X1) | ~r1_tarski(sK9,u1_struct_0(X1))) )),
% 1.44/0.57    inference(resolution,[],[f402,f100])).
% 1.44/0.57  fof(f100,plain,(
% 1.44/0.57    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.44/0.57    inference(definition_unfolding,[],[f59,f63])).
% 1.44/0.57  fof(f59,plain,(
% 1.44/0.57    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.44/0.57    inference(cnf_transformation,[],[f40])).
% 1.44/0.57  fof(f402,plain,(
% 1.44/0.57    ( ! [X17,X18,X16] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X18))) | ~v3_pre_topc(X17,X18) | sP4(X17,X16,X18) | ~l1_struct_0(X16) | ~r1_tarski(X17,u1_struct_0(X16))) )),
% 1.44/0.57    inference(subsumption_resolution,[],[f395,f107])).
% 1.44/0.57  fof(f107,plain,(
% 1.44/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(forward_demodulation,[],[f66,f65])).
% 1.44/0.57  fof(f65,plain,(
% 1.44/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f2])).
% 1.44/0.57  fof(f2,axiom,(
% 1.44/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.44/0.57  fof(f66,plain,(
% 1.44/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f3])).
% 1.44/0.57  fof(f3,axiom,(
% 1.44/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.44/0.57  fof(f395,plain,(
% 1.44/0.57    ( ! [X17,X18,X16] : (sP4(X17,X16,X18) | ~v3_pre_topc(X17,X18) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X18))) | ~l1_struct_0(X16) | ~m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X16))) | ~r1_tarski(X17,u1_struct_0(X16))) )),
% 1.44/0.57    inference(superposition,[],[f225,f176])).
% 1.44/0.57  fof(f176,plain,(
% 1.44/0.57    ( ! [X6,X4,X5] : (k9_subset_1(X6,X4,X5) = X4 | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~r1_tarski(X4,X5)) )),
% 1.44/0.57    inference(superposition,[],[f102,f101])).
% 1.44/0.57  fof(f101,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(definition_unfolding,[],[f95,f94])).
% 1.44/0.57  fof(f94,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f5])).
% 1.44/0.57  fof(f5,axiom,(
% 1.44/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.44/0.57  fof(f95,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f24])).
% 1.44/0.57  fof(f24,plain,(
% 1.44/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.57    inference(ennf_transformation,[],[f1])).
% 1.44/0.57  fof(f1,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.57  fof(f102,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f98,f94])).
% 1.44/0.57  fof(f98,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f27])).
% 1.44/0.57  fof(f27,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f4])).
% 1.44/0.57  fof(f4,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.44/0.57  fof(f225,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (sP4(k9_subset_1(u1_struct_0(X0),X1,u1_struct_0(X0)),X0,X2) | ~v3_pre_topc(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_struct_0(X0)) )),
% 1.44/0.57    inference(superposition,[],[f104,f67])).
% 1.44/0.57  fof(f67,plain,(
% 1.44/0.57    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f17])).
% 1.44/0.57  fof(f17,plain,(
% 1.44/0.57    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f7])).
% 1.44/0.57  fof(f7,axiom,(
% 1.44/0.57    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.44/0.57  fof(f104,plain,(
% 1.44/0.57    ( ! [X2,X3,X1] : (sP4(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X2) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.44/0.57    inference(equality_resolution,[],[f90])).
% 1.44/0.57  fof(f90,plain,(
% 1.44/0.57    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f56])).
% 1.44/0.57  fof(f56,plain,(
% 1.44/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X1),sK12(X0,X1,X2),k2_struct_0(X1)) = X0 & v3_pre_topc(sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP4(X0,X1,X2)))),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f54,f55])).
% 1.44/0.57  fof(f55,plain,(
% 1.44/0.57    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X1),sK12(X0,X1,X2),k2_struct_0(X1)) = X0 & v3_pre_topc(sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f54,plain,(
% 1.44/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP4(X0,X1,X2)))),
% 1.44/0.57    inference(rectify,[],[f53])).
% 1.44/0.57  fof(f53,plain,(
% 1.44/0.57    ! [X2,X1,X0] : ((sP4(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP4(X2,X1,X0)))),
% 1.44/0.57    inference(nnf_transformation,[],[f33])).
% 1.44/0.57  fof(f432,plain,(
% 1.44/0.57    spl13_6),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f431])).
% 1.44/0.57  fof(f431,plain,(
% 1.44/0.57    $false | spl13_6),
% 1.44/0.57    inference(subsumption_resolution,[],[f430,f109])).
% 1.44/0.57  fof(f109,plain,(
% 1.44/0.57    l1_pre_topc(sK8)),
% 1.44/0.57    inference(subsumption_resolution,[],[f108,f58])).
% 1.44/0.57  fof(f108,plain,(
% 1.44/0.57    l1_pre_topc(sK8) | ~l1_pre_topc(sK6)),
% 1.44/0.57    inference(resolution,[],[f84,f60])).
% 1.44/0.57  fof(f84,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f20])).
% 1.44/0.57  fof(f20,plain,(
% 1.44/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f11])).
% 1.44/0.57  fof(f11,axiom,(
% 1.44/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.44/0.57  fof(f430,plain,(
% 1.44/0.57    ~l1_pre_topc(sK8) | spl13_6),
% 1.44/0.57    inference(resolution,[],[f424,f68])).
% 1.44/0.57  fof(f68,plain,(
% 1.44/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f18])).
% 1.44/0.57  fof(f18,plain,(
% 1.44/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f10])).
% 1.44/0.57  fof(f10,axiom,(
% 1.44/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.44/0.57  fof(f424,plain,(
% 1.44/0.57    ~l1_struct_0(sK8) | spl13_6),
% 1.44/0.57    inference(avatar_component_clause,[],[f422])).
% 1.44/0.57  fof(f429,plain,(
% 1.44/0.57    ~spl13_6 | spl13_7),
% 1.44/0.57    inference(avatar_split_clause,[],[f420,f426,f422])).
% 1.44/0.57  fof(f420,plain,(
% 1.44/0.57    r1_tarski(sK9,u1_struct_0(sK8)) | ~l1_struct_0(sK8)),
% 1.44/0.57    inference(superposition,[],[f417,f67])).
% 1.44/0.57  fof(f417,plain,(
% 1.44/0.57    r1_tarski(sK9,k2_struct_0(sK8))),
% 1.44/0.57    inference(subsumption_resolution,[],[f410,f109])).
% 1.44/0.57  fof(f410,plain,(
% 1.44/0.57    ~l1_pre_topc(sK8) | r1_tarski(sK9,k2_struct_0(sK8))),
% 1.44/0.57    inference(resolution,[],[f409,f62])).
% 1.44/0.58  fof(f409,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | r1_tarski(X0,k2_struct_0(X1))) )),
% 1.44/0.58    inference(duplicate_literal_removal,[],[f408])).
% 1.44/0.58  fof(f408,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | r1_tarski(X0,k2_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 1.44/0.58    inference(resolution,[],[f344,f97])).
% 1.44/0.58  fof(f97,plain,(
% 1.44/0.58    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f26])).
% 1.44/0.58  fof(f26,plain,(
% 1.44/0.58    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.58    inference(flattening,[],[f25])).
% 1.44/0.58  fof(f25,plain,(
% 1.44/0.58    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.44/0.58    inference(ennf_transformation,[],[f9])).
% 1.44/0.58  fof(f9,axiom,(
% 1.44/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.44/0.58  fof(f344,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_pre_topc(X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | r1_tarski(X0,k2_struct_0(X1)) | ~l1_pre_topc(X1)) )),
% 1.44/0.58    inference(resolution,[],[f334,f113])).
% 1.44/0.58  fof(f113,plain,(
% 1.44/0.58    ( ! [X0,X1] : (sP2(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f112,f84])).
% 1.44/0.58  fof(f112,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 1.44/0.58    inference(resolution,[],[f69,f83])).
% 1.44/0.58  fof(f83,plain,(
% 1.44/0.58    ( ! [X0,X1] : (sP3(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f32])).
% 1.44/0.58  fof(f32,plain,(
% 1.44/0.58    ! [X0] : (! [X1] : (sP3(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.44/0.58    inference(definition_folding,[],[f19,f31,f30,f29,f28])).
% 1.44/0.58  fof(f28,plain,(
% 1.44/0.58    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.58  fof(f29,plain,(
% 1.44/0.58    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> sP0(X2,X1,X0)))),
% 1.44/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.58  fof(f30,plain,(
% 1.44/0.58    ! [X1,X0] : (sP2(X1,X0) <=> (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 1.44/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.44/0.58  fof(f31,plain,(
% 1.44/0.58    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 1.44/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.44/0.58  fof(f19,plain,(
% 1.44/0.58    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.44/0.58    inference(ennf_transformation,[],[f8])).
% 1.44/0.58  fof(f8,axiom,(
% 1.44/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 1.44/0.58  fof(f69,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~sP3(X0,X1) | ~m1_pre_topc(X1,X0) | sP2(X1,X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f41])).
% 1.44/0.58  fof(f41,plain,(
% 1.44/0.58    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP3(X0,X1))),
% 1.44/0.58    inference(nnf_transformation,[],[f31])).
% 1.44/0.58  fof(f334,plain,(
% 1.44/0.58    ( ! [X4,X2,X3] : (~sP2(k1_pre_topc(X2,X3),X4) | r1_tarski(X3,k2_struct_0(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.44/0.58    inference(superposition,[],[f71,f331])).
% 1.44/0.58  fof(f331,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f330,f97])).
% 1.44/0.58  fof(f330,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(subsumption_resolution,[],[f106,f96])).
% 1.44/0.58  fof(f96,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f26])).
% 1.44/0.58  fof(f106,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(equality_resolution,[],[f92])).
% 1.44/0.58  fof(f92,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f57])).
% 1.44/0.58  fof(f57,plain,(
% 1.44/0.58    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.58    inference(nnf_transformation,[],[f23])).
% 1.44/0.58  fof(f23,plain,(
% 1.44/0.58    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.58    inference(flattening,[],[f22])).
% 1.44/0.58  fof(f22,plain,(
% 1.44/0.58    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.58    inference(ennf_transformation,[],[f6])).
% 1.44/0.58  fof(f6,axiom,(
% 1.44/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 1.44/0.58  fof(f71,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP2(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f46])).
% 1.44/0.58  fof(f46,plain,(
% 1.44/0.58    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0,sK10(X0,X1)) & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 1.44/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).
% 1.44/0.58  fof(f45,plain,(
% 1.44/0.58    ! [X1,X0] : (? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP1(X1,X0,sK10(X0,X1)) & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.58    introduced(choice_axiom,[])).
% 1.44/0.58  fof(f44,plain,(
% 1.44/0.58    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 1.44/0.58    inference(rectify,[],[f43])).
% 1.44/0.58  fof(f43,plain,(
% 1.44/0.58    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 1.44/0.58    inference(flattening,[],[f42])).
% 1.44/0.58  fof(f42,plain,(
% 1.44/0.58    ! [X1,X0] : ((sP2(X1,X0) | (? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 1.44/0.58    inference(nnf_transformation,[],[f30])).
% 1.44/0.58  % SZS output end Proof for theBenchmark
% 1.44/0.58  % (22557)------------------------------
% 1.44/0.58  % (22557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (22557)Termination reason: Refutation
% 1.44/0.58  
% 1.44/0.58  % (22557)Memory used [KB]: 6524
% 1.44/0.58  % (22557)Time elapsed: 0.162 s
% 1.44/0.58  % (22557)------------------------------
% 1.44/0.58  % (22557)------------------------------
% 1.44/0.58  % (22529)Success in time 0.224 s
%------------------------------------------------------------------------------
