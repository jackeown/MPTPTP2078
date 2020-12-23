%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 178 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  365 ( 723 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f76,f83,f87,f112,f113,f136,f147,f160,f163])).

fof(f163,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_17 ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f158,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_17
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f160,plain,
    ( ~ spl4_17
    | ~ spl4_10
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f153,f145,f85,f110,f157])).

fof(f110,plain,
    ( spl4_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f145,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f153,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(resolution,[],[f146,f86])).

fof(f86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_15
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f141,f134,f145,f65,f69])).

fof(f69,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f65,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f134,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_14 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_14 ),
    inference(superposition,[],[f135,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f51,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_subset_1(k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f50,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f48,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f135,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl4_7
    | ~ spl4_10
    | spl4_14
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f125,f106,f65,f134,f110,f81])).

fof(f81,plain,
    ( spl4_7
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(superposition,[],[f123,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != sK2(sK0,X0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f122,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_xboole_0(X1,X2) != sK2(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) != sK2(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f45,f51])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v3_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f112,plain,
    ( spl4_9
    | spl4_7
    | ~ spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f104,f65,f110,f81,f106])).

fof(f104,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(k1_xboole_0,sK0)
    | k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(resolution,[],[f103,f46])).

fof(f103,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f44,f66])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f79,f74,f61,f85])).

fof(f61,plain,
    ( spl4_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f74,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(superposition,[],[f62,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f62,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f83,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f78,f74,f53,f81])).

fof(f53,plain,
    ( spl4_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f54,f75])).

fof(f54,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f72,f61,f74])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3 ),
    inference(resolution,[],[f39,f62])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f57])).

fof(f57,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f53])).

fof(f37,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (23293)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (23280)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (23280)Refutation not found, incomplete strategy% (23280)------------------------------
% 0.21/0.47  % (23280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23280)Memory used [KB]: 6140
% 0.21/0.47  % (23280)Time elapsed: 0.052 s
% 0.21/0.47  % (23280)------------------------------
% 0.21/0.47  % (23280)------------------------------
% 0.21/0.47  % (23292)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (23290)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (23282)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (23294)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (23284)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (23287)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (23295)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (23285)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (23299)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (23286)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (23281)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (23291)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (23281)Refutation not found, incomplete strategy% (23281)------------------------------
% 0.21/0.51  % (23281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23281)Memory used [KB]: 10618
% 0.21/0.51  % (23281)Time elapsed: 0.093 s
% 0.21/0.51  % (23281)------------------------------
% 0.21/0.51  % (23281)------------------------------
% 0.21/0.51  % (23291)Refutation not found, incomplete strategy% (23291)------------------------------
% 0.21/0.51  % (23291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23291)Memory used [KB]: 10618
% 0.21/0.51  % (23291)Time elapsed: 0.091 s
% 0.21/0.51  % (23291)------------------------------
% 0.21/0.51  % (23291)------------------------------
% 0.21/0.51  % (23286)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f76,f83,f87,f112,f113,f136,f147,f160,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl4_17),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    $false | spl4_17),
% 0.21/0.51    inference(resolution,[],[f158,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl4_17 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ~spl4_17 | ~spl4_10 | ~spl4_8 | ~spl4_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f153,f145,f85,f110,f157])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl4_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl4_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl4_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_8 | ~spl4_15)),
% 0.21/0.51    inference(resolution,[],[f146,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~spl4_5 | ~spl4_4 | spl4_15 | ~spl4_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f141,f134,f145,f65,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl4_5 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl4_4 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl4_14 <=> ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_14),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_14),
% 0.21/0.51    inference(resolution,[],[f138,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_14),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_14),
% 0.21/0.51    inference(superposition,[],[f135,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.51    inference(superposition,[],[f51,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.51    inference(resolution,[],[f50,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f48,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | ~spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl4_7 | ~spl4_10 | spl4_14 | ~spl4_4 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f125,f106,f65,f134,f110,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl4_7 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl4_9 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.51    inference(superposition,[],[f123,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != sK2(sK0,X0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f122,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_xboole_0(X1,X2) != sK2(X0,X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | v2_tex_2(X1,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(superposition,[],[f45,f51])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(rectify,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl4_9 | spl4_7 | ~spl4_10 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f104,f65,f110,f81,f106])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_xboole_0,sK0) | k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f103,f46])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f44,f66])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl4_8 | ~spl4_3 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f74,f61,f85])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl4_3 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl4_6 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | (~spl4_3 | ~spl4_6)),
% 0.21/0.51    inference(superposition,[],[f62,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~spl4_7 | spl4_1 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f78,f74,f53,f81])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl4_1 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~v2_tex_2(k1_xboole_0,sK0) | (spl4_1 | ~spl4_6)),
% 0.21/0.51    inference(superposition,[],[f54,f75])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~v2_tex_2(sK1,sK0) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl4_6 | ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f72,f61,f74])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f39,f62])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f69])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f65])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f61])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f53])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ~v2_tex_2(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23286)------------------------------
% 0.21/0.51  % (23286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23286)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23286)Memory used [KB]: 10746
% 0.21/0.51  % (23286)Time elapsed: 0.060 s
% 0.21/0.51  % (23286)------------------------------
% 0.21/0.51  % (23286)------------------------------
% 0.21/0.51  % (23289)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (23279)Success in time 0.157 s
%------------------------------------------------------------------------------
