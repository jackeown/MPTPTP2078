%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:56 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 364 expanded)
%              Number of leaves         :   24 ( 136 expanded)
%              Depth                    :   11
%              Number of atoms          :  289 (1238 expanded)
%              Number of equality atoms :   16 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f121,f132,f135,f153,f179,f182,f196,f202,f218,f232,f257])).

fof(f257,plain,
    ( ~ spl4_11
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl4_11
    | spl4_15 ),
    inference(resolution,[],[f213,f197])).

fof(f197,plain,
    ( m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f147,f185])).

fof(f185,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(resolution,[],[f88,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f35,f61])).

fof(f61,plain,(
    ! [X0] : sK3(X0) = X0 ),
    inference(resolution,[],[f58,f35])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | sK3(X0) = X0 ) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK3(X0),X0)
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X26,X25] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X25))
      | k9_subset_1(X25,X26,sK2) = k9_subset_1(u1_struct_0(sK0),X26,sK2) ) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X3))
      | k9_subset_1(X2,X0,X1) = k9_subset_1(X3,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f47,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f147,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_11
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f213,plain,
    ( ~ m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl4_15
  <=> m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f232,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f227,f64])).

fof(f227,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl4_16 ),
    inference(resolution,[],[f217,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X2,X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f46,f47])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f217,plain,
    ( ~ r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl4_16
  <=> r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f218,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f206,f200,f215,f211])).

fof(f200,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f206,plain,
    ( ~ r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1)
    | ~ m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(resolution,[],[f201,f190])).

fof(f190,plain,(
    ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f33,f185])).

fof(f33,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f201,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( ~ spl4_3
    | spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f198,f50,f200,f100])).

fof(f100,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f50,plain,
    ( spl4_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f52,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X1,sK0) ) ),
    inference(resolution,[],[f34,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f52,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f196,plain,
    ( ~ spl4_13
    | ~ spl4_8
    | spl4_11 ),
    inference(avatar_split_clause,[],[f195,f146,f126,f176])).

fof(f176,plain,
    ( spl4_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f126,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f195,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl4_11 ),
    inference(resolution,[],[f189,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_subset_1(X2,X0,X1),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f72,f47])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f43,f47])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f189,plain,
    ( ~ m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_11 ),
    inference(backward_demodulation,[],[f148,f185])).

fof(f148,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f182,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f178,f64])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f176])).

fof(f179,plain,
    ( ~ spl4_8
    | ~ spl4_13
    | spl4_12 ),
    inference(avatar_split_clause,[],[f174,f150,f176,f126])).

fof(f150,plain,
    ( spl4_12
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(resolution,[],[f160,f78])).

fof(f160,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2))
    | spl4_12 ),
    inference(resolution,[],[f152,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

% (29665)Refutation not found, incomplete strategy% (29665)------------------------------
% (29665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f152,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f150])).

% (29665)Termination reason: Refutation not found, incomplete strategy
fof(f153,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f137,f130,f150,f146])).

% (29665)Memory used [KB]: 10746
% (29665)Time elapsed: 0.132 s
fof(f130,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

% (29665)------------------------------
% (29665)------------------------------
fof(f137,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(resolution,[],[f131,f33])).

fof(f131,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f135,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f128,f31])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f132,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f124,f54,f130,f126])).

fof(f54,plain,
    ( spl4_2
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f89,f56])).

fof(f56,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f121,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f102,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f57,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f32,f54,f50])).

fof(f32,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:30:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (29652)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (29668)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (29645)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29655)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (29651)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (29653)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.53  % (29647)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.53  % (29669)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.53  % (29650)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.53  % (29665)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.53  % (29644)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (29655)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f258,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(avatar_sat_refutation,[],[f57,f121,f132,f135,f153,f179,f182,f196,f202,f218,f232,f257])).
% 1.32/0.53  fof(f257,plain,(
% 1.32/0.53    ~spl4_11 | spl4_15),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f254])).
% 1.32/0.53  fof(f254,plain,(
% 1.32/0.53    $false | (~spl4_11 | spl4_15)),
% 1.32/0.53    inference(resolution,[],[f213,f197])).
% 1.32/0.53  fof(f197,plain,(
% 1.32/0.53    m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_11),
% 1.32/0.53    inference(forward_demodulation,[],[f147,f185])).
% 1.32/0.53  fof(f185,plain,(
% 1.32/0.53    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)) )),
% 1.32/0.53    inference(resolution,[],[f88,f64])).
% 1.32/0.53  fof(f64,plain,(
% 1.32/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.32/0.53    inference(backward_demodulation,[],[f35,f61])).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    ( ! [X0] : (sK3(X0) = X0) )),
% 1.32/0.53    inference(resolution,[],[f58,f35])).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X0] : (~m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) | sK3(X0) = X0) )),
% 1.32/0.53    inference(resolution,[],[f40,f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ! [X0] : (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(nnf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,plain,(
% 1.32/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f26])).
% 1.32/0.54  fof(f88,plain,(
% 1.32/0.54    ( ! [X26,X25] : (~m1_subset_1(sK2,k1_zfmisc_1(X25)) | k9_subset_1(X25,X26,sK2) = k9_subset_1(u1_struct_0(sK0),X26,sK2)) )),
% 1.32/0.54    inference(resolution,[],[f68,f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f13,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f12])).
% 1.32/0.54  fof(f12,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,negated_conjecture,(
% 1.32/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.32/0.54    inference(negated_conjecture,[],[f10])).
% 1.32/0.54  fof(f10,conjecture,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X3)) | k9_subset_1(X2,X0,X1) = k9_subset_1(X3,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 1.32/0.54    inference(superposition,[],[f47,f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f44,f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.32/0.54  fof(f147,plain,(
% 1.32/0.54    m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f146])).
% 1.32/0.54  fof(f146,plain,(
% 1.32/0.54    spl4_11 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.32/0.54  fof(f213,plain,(
% 1.32/0.54    ~m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_15),
% 1.32/0.54    inference(avatar_component_clause,[],[f211])).
% 1.32/0.54  fof(f211,plain,(
% 1.32/0.54    spl4_15 <=> m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.32/0.54  fof(f232,plain,(
% 1.32/0.54    spl4_16),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f230])).
% 1.32/0.54  fof(f230,plain,(
% 1.32/0.54    $false | spl4_16),
% 1.32/0.54    inference(resolution,[],[f227,f64])).
% 1.32/0.54  fof(f227,plain,(
% 1.32/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl4_16),
% 1.32/0.54    inference(resolution,[],[f217,f70])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X2,X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 1.32/0.54    inference(superposition,[],[f46,f47])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f37,f38])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.32/0.54  fof(f217,plain,(
% 1.32/0.54    ~r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1) | spl4_16),
% 1.32/0.54    inference(avatar_component_clause,[],[f215])).
% 1.32/0.54  fof(f215,plain,(
% 1.32/0.54    spl4_16 <=> r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.32/0.54  fof(f218,plain,(
% 1.32/0.54    ~spl4_15 | ~spl4_16 | ~spl4_14),
% 1.32/0.54    inference(avatar_split_clause,[],[f206,f200,f215,f211])).
% 1.32/0.54  fof(f200,plain,(
% 1.32/0.54    spl4_14 <=> ! [X0] : (~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.32/0.54  fof(f206,plain,(
% 1.32/0.54    ~r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1) | ~m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_14),
% 1.32/0.54    inference(resolution,[],[f201,f190])).
% 1.32/0.54  fof(f190,plain,(
% 1.32/0.54    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)),
% 1.32/0.54    inference(backward_demodulation,[],[f33,f185])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f201,plain,(
% 1.32/0.54    ( ! [X0] : (v2_tex_2(X0,sK0) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_14),
% 1.32/0.54    inference(avatar_component_clause,[],[f200])).
% 1.32/0.54  fof(f202,plain,(
% 1.32/0.54    ~spl4_3 | spl4_14 | ~spl4_1),
% 1.32/0.54    inference(avatar_split_clause,[],[f198,f50,f200,f100])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    spl4_1 <=> v2_tex_2(sK1,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.54  fof(f198,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl4_1),
% 1.32/0.54    inference(resolution,[],[f52,f89])).
% 1.32/0.54  fof(f89,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) )),
% 1.32/0.54    inference(resolution,[],[f34,f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    l1_pre_topc(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f14])).
% 1.32/0.54  fof(f14,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    v2_tex_2(sK1,sK0) | ~spl4_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f50])).
% 1.32/0.54  fof(f196,plain,(
% 1.32/0.54    ~spl4_13 | ~spl4_8 | spl4_11),
% 1.32/0.54    inference(avatar_split_clause,[],[f195,f146,f126,f176])).
% 1.32/0.54  fof(f176,plain,(
% 1.32/0.54    spl4_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.32/0.54  fof(f126,plain,(
% 1.32/0.54    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.32/0.54  fof(f195,plain,(
% 1.32/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl4_11),
% 1.32/0.54    inference(resolution,[],[f189,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(k9_subset_1(X2,X0,X1),k1_zfmisc_1(X3)) | ~m1_subset_1(X1,k1_zfmisc_1(X3)) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 1.32/0.54    inference(superposition,[],[f72,f47])).
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f69])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(superposition,[],[f43,f47])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f17])).
% 1.32/0.54  fof(f17,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.32/0.54  fof(f189,plain,(
% 1.32/0.54    ~m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_11),
% 1.32/0.54    inference(backward_demodulation,[],[f148,f185])).
% 1.32/0.54  fof(f148,plain,(
% 1.32/0.54    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f146])).
% 1.32/0.54  fof(f182,plain,(
% 1.32/0.54    spl4_13),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f180])).
% 1.32/0.54  fof(f180,plain,(
% 1.32/0.54    $false | spl4_13),
% 1.32/0.54    inference(resolution,[],[f178,f64])).
% 1.32/0.54  fof(f178,plain,(
% 1.32/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl4_13),
% 1.32/0.54    inference(avatar_component_clause,[],[f176])).
% 1.32/0.54  fof(f179,plain,(
% 1.32/0.54    ~spl4_8 | ~spl4_13 | spl4_12),
% 1.32/0.54    inference(avatar_split_clause,[],[f174,f150,f176,f126])).
% 1.32/0.54  fof(f150,plain,(
% 1.32/0.54    spl4_12 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.32/0.54  fof(f174,plain,(
% 1.32/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_12),
% 1.32/0.54    inference(resolution,[],[f160,f78])).
% 1.32/0.54  fof(f160,plain,(
% 1.32/0.54    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2)) | spl4_12),
% 1.32/0.54    inference(resolution,[],[f152,f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.32/0.54    inference(nnf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.32/0.54  % (29665)Refutation not found, incomplete strategy% (29665)------------------------------
% 1.32/0.54  % (29665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  fof(f152,plain,(
% 1.32/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | spl4_12),
% 1.32/0.54    inference(avatar_component_clause,[],[f150])).
% 1.32/0.54  % (29665)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  fof(f153,plain,(
% 1.32/0.54    ~spl4_11 | ~spl4_12 | ~spl4_9),
% 1.32/0.54    inference(avatar_split_clause,[],[f137,f130,f150,f146])).
% 1.32/0.54  
% 1.32/0.54  % (29665)Memory used [KB]: 10746
% 1.32/0.54  % (29665)Time elapsed: 0.132 s
% 1.32/0.54  fof(f130,plain,(
% 1.32/0.54    spl4_9 <=> ! [X0] : (~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.32/0.54  % (29665)------------------------------
% 1.32/0.54  % (29665)------------------------------
% 1.32/0.54  fof(f137,plain,(
% 1.32/0.54    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 1.32/0.54    inference(resolution,[],[f131,f33])).
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    ( ! [X0] : (v2_tex_2(X0,sK0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_9),
% 1.32/0.54    inference(avatar_component_clause,[],[f130])).
% 1.32/0.54  fof(f135,plain,(
% 1.32/0.54    spl4_8),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f133])).
% 1.32/0.54  fof(f133,plain,(
% 1.32/0.54    $false | spl4_8),
% 1.32/0.54    inference(resolution,[],[f128,f31])).
% 1.32/0.54  fof(f128,plain,(
% 1.32/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_8),
% 1.32/0.54    inference(avatar_component_clause,[],[f126])).
% 1.32/0.54  fof(f132,plain,(
% 1.32/0.54    ~spl4_8 | spl4_9 | ~spl4_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f124,f54,f130,f126])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    spl4_2 <=> v2_tex_2(sK2,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.54  fof(f124,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl4_2),
% 1.32/0.54    inference(resolution,[],[f89,f56])).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    v2_tex_2(sK2,sK0) | ~spl4_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f54])).
% 1.32/0.54  fof(f121,plain,(
% 1.32/0.54    spl4_3),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f119])).
% 1.32/0.54  fof(f119,plain,(
% 1.32/0.54    $false | spl4_3),
% 1.32/0.54    inference(resolution,[],[f102,f30])).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f102,plain,(
% 1.32/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f100])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    spl4_1 | spl4_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f32,f54,f50])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (29655)------------------------------
% 1.32/0.54  % (29655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (29655)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (29655)Memory used [KB]: 6396
% 1.32/0.54  % (29655)Time elapsed: 0.113 s
% 1.32/0.54  % (29655)------------------------------
% 1.32/0.54  % (29655)------------------------------
% 1.32/0.54  % (29667)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (29643)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (29659)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (29664)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.54  % (29648)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (29657)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (29649)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (29654)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (29672)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (29663)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (29661)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.55  % (29670)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.55  % (29646)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.55  % (29671)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.55  % (29662)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.55  % (29660)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.56  % (29642)Success in time 0.197 s
%------------------------------------------------------------------------------
