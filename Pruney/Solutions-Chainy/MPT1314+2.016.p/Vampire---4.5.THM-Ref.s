%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 321 expanded)
%              Number of leaves         :   22 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  317 (1432 expanded)
%              Number of equality atoms :   52 ( 287 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f85,f164,f182,f189,f192,f196])).

fof(f196,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl5_13 ),
    inference(resolution,[],[f177,f37])).

fof(f37,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f24,f23,f22,f21])).

fof(f21,plain,
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
              & v3_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v3_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v3_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f177,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_13
  <=> v3_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f192,plain,
    ( ~ spl5_2
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl5_2
    | spl5_14 ),
    inference(resolution,[],[f181,f87])).

fof(f87,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f35,f81])).

fof(f81,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f181,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f189,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f173,f61])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f53,f59])).

fof(f59,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f58,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f182,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f169,f162,f79,f179,f175,f171])).

fof(f162,plain,
    ( spl5_11
  <=> ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f169,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f168,f117])).

fof(f117,plain,
    ( sK3 = k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2))
    | ~ spl5_2 ),
    inference(superposition,[],[f95,f63])).

fof(f63,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f95,plain,
    ( sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_struct_0(sK2)))
    | ~ spl5_2 ),
    inference(resolution,[],[f90,f87])).

fof(f90,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k4_xboole_0(X3,k4_xboole_0(X3,X2)) = X3 ) ),
    inference(superposition,[],[f72,f63])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k9_subset_1(X0,X1,X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f69,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k9_subset_1(X3,X2,X3) = X2 ) ),
    inference(superposition,[],[f63,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f168,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f166,f117])).

fof(f166,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_11 ),
    inference(resolution,[],[f163,f52])).

fof(f52,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( ~ spl5_1
    | spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f160,f79,f162,f75])).

fof(f75,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f160,plain,
    ( ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f159,f81])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f158,f81])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f157,f59])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f56,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f85,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f77,f31])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f82,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f73,f79,f75])).

fof(f73,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (11751)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (11751)Refutation not found, incomplete strategy% (11751)------------------------------
% 0.21/0.47  % (11751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (11751)Memory used [KB]: 10746
% 0.21/0.47  % (11751)Time elapsed: 0.071 s
% 0.21/0.47  % (11751)------------------------------
% 0.21/0.47  % (11751)------------------------------
% 0.21/0.48  % (11775)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.48  % (11761)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (11761)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (11775)Refutation not found, incomplete strategy% (11775)------------------------------
% 0.21/0.49  % (11775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11775)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11775)Memory used [KB]: 10874
% 0.21/0.49  % (11775)Time elapsed: 0.101 s
% 0.21/0.49  % (11775)------------------------------
% 0.21/0.49  % (11775)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f82,f85,f164,f182,f189,f192,f196])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~spl5_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    $false | ~spl5_13),
% 0.21/0.49    inference(resolution,[],[f177,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~v3_pre_topc(sK3,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    (((~v3_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f24,f23,f22,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v3_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v3_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X3] : (~v3_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v3_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    v3_pre_topc(sK3,sK2) | ~spl5_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl5_13 <=> v3_pre_topc(sK3,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ~spl5_2 | spl5_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    $false | (~spl5_2 | spl5_14)),
% 0.21/0.49    inference(resolution,[],[f181,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | ~spl5_2),
% 0.21/0.49    inference(backward_demodulation,[],[f35,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl5_2 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl5_14 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    spl5_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    $false | spl5_12),
% 0.21/0.49    inference(resolution,[],[f173,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f53,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f58,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f40,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    sK1 = sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | spl5_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl5_12 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_2 | ~spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f169,f162,f79,f179,f175,f171])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl5_11 <=> ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) | v3_pre_topc(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_2 | ~spl5_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f168,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    sK3 = k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)) | ~spl5_2),
% 0.21/0.49    inference(superposition,[],[f95,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(resolution,[],[f55,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f39,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f51,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_struct_0(sK2))) | ~spl5_2),
% 0.21/0.49    inference(resolution,[],[f90,f87])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k4_xboole_0(X3,k4_xboole_0(X3,X2)) = X3) )),
% 0.21/0.49    inference(superposition,[],[f72,f63])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f69,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_subset_1(X3,X2,X3) = X2) )),
% 0.21/0.49    inference(superposition,[],[f63,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f48,f47])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    v3_pre_topc(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | (~spl5_2 | ~spl5_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f166,f117])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~spl5_11),
% 0.21/0.49    inference(resolution,[],[f163,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v3_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f36])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v3_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))) ) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~spl5_1 | spl5_11 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f160,f79,f162,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl5_2),
% 0.21/0.49    inference(forward_demodulation,[],[f159,f81])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) ) | ~spl5_2),
% 0.21/0.49    inference(forward_demodulation,[],[f158,f81])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f157,f59])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f56,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    $false | spl5_1),
% 0.21/0.49    inference(resolution,[],[f77,f31])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl5_1 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f79,f75])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_struct_0(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f60,f33])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f58,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11761)------------------------------
% 0.21/0.49  % (11761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11761)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11761)Memory used [KB]: 6268
% 0.21/0.49  % (11761)Time elapsed: 0.102 s
% 0.21/0.49  % (11761)------------------------------
% 0.21/0.49  % (11761)------------------------------
% 0.21/0.50  % (11748)Success in time 0.135 s
%------------------------------------------------------------------------------
