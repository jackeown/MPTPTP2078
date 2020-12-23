%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:10 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 176 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  367 ( 725 expanded)
%              Number of equality atoms :   46 (  77 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f78,f84,f115,f118,f130,f141,f149,f151])).

fof(f151,plain,
    ( ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f61,f126])).

fof(f126,plain,
    ( ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_11
  <=> ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_6
    | spl5_13 ),
    inference(avatar_split_clause,[],[f145,f139,f76,f110,f68,f72])).

fof(f72,plain,
    ( spl5_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f68,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f110,plain,
    ( spl5_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f76,plain,
    ( spl5_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f139,plain,
    ( spl5_13
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f145,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_13 ),
    inference(resolution,[],[f140,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f140,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( ~ spl5_9
    | ~ spl5_13
    | spl5_1
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f137,f128,f113,f82,f56,f139,f110])).

fof(f56,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f82,plain,
    ( spl5_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f113,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f128,plain,
    ( spl5_12
  <=> ! [X0] :
        ( v2_tex_2(X0,sK0)
        | sK2(sK0,X0) != X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f137,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f136,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f136,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f135,f83])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f133,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f133,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f131,f83])).

fof(f131,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | spl5_1
    | ~ spl5_12 ),
    inference(resolution,[],[f129,f57])).

fof(f57,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f129,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | sK2(sK0,X0) != X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f123,f68,f128,f125])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK2(sK0,X0) != X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f122,f69])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sK2(X0,X1) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1) != X1
      | v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f48,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v4_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f118,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f115,plain,
    ( ~ spl5_9
    | spl5_10
    | spl5_1
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f108,f82,f68,f56,f113,f110])).

fof(f108,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f107,f92])).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f107,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK2(sK0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f106,f83])).

fof(f106,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_xboole_0(sK1,sK2(sK0,sK1))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f104,f83])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_xboole_0(sK1,sK2(sK0,sK1))
    | spl5_1
    | ~ spl5_4 ),
    inference(resolution,[],[f103,f57])).

fof(f103,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(X0,sK2(sK0,X0)) = X0 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f102,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | k2_xboole_0(sK2(sK0,X0),X0) = X0 )
    | ~ spl5_4 ),
    inference(resolution,[],[f101,f53])).

fof(f101,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f47,f69])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f79,f64,f82])).

fof(f64,plain,
    ( spl5_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(resolution,[],[f49,f65])).

% (13912)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f65,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f78,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f70,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f60])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f56])).

fof(f39,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:40:54 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.38  ipcrm: permission denied for id (824836100)
% 0.21/0.38  ipcrm: permission denied for id (823459845)
% 0.21/0.39  ipcrm: permission denied for id (824934408)
% 0.21/0.39  ipcrm: permission denied for id (823525386)
% 0.21/0.39  ipcrm: permission denied for id (824999947)
% 0.21/0.39  ipcrm: permission denied for id (825065485)
% 0.21/0.40  ipcrm: permission denied for id (825098254)
% 0.21/0.40  ipcrm: permission denied for id (825163792)
% 0.21/0.40  ipcrm: permission denied for id (825229330)
% 0.21/0.40  ipcrm: permission denied for id (825294868)
% 0.21/0.40  ipcrm: permission denied for id (825360405)
% 0.21/0.41  ipcrm: permission denied for id (825393174)
% 0.21/0.41  ipcrm: permission denied for id (825425943)
% 0.21/0.41  ipcrm: permission denied for id (823689241)
% 0.21/0.41  ipcrm: permission denied for id (823722011)
% 0.21/0.41  ipcrm: permission denied for id (825557021)
% 0.21/0.42  ipcrm: permission denied for id (825622559)
% 0.21/0.42  ipcrm: permission denied for id (825655328)
% 0.21/0.42  ipcrm: permission denied for id (825688097)
% 0.21/0.42  ipcrm: permission denied for id (825720866)
% 0.21/0.42  ipcrm: permission denied for id (823820324)
% 0.21/0.42  ipcrm: permission denied for id (825851943)
% 0.21/0.42  ipcrm: permission denied for id (825884712)
% 0.21/0.43  ipcrm: permission denied for id (825950250)
% 0.21/0.43  ipcrm: permission denied for id (826015788)
% 0.21/0.43  ipcrm: permission denied for id (823918637)
% 0.21/0.43  ipcrm: permission denied for id (826048558)
% 0.21/0.43  ipcrm: permission denied for id (826081327)
% 0.21/0.43  ipcrm: permission denied for id (826114096)
% 0.21/0.43  ipcrm: permission denied for id (824016946)
% 0.21/0.43  ipcrm: permission denied for id (824049715)
% 0.21/0.44  ipcrm: permission denied for id (826212405)
% 0.21/0.44  ipcrm: permission denied for id (826245174)
% 0.21/0.44  ipcrm: permission denied for id (826310712)
% 0.21/0.44  ipcrm: permission denied for id (824082491)
% 0.21/0.44  ipcrm: permission denied for id (826409020)
% 0.21/0.44  ipcrm: permission denied for id (826441789)
% 0.21/0.45  ipcrm: permission denied for id (826671171)
% 0.21/0.45  ipcrm: permission denied for id (824180805)
% 0.21/0.45  ipcrm: permission denied for id (824213574)
% 0.21/0.45  ipcrm: permission denied for id (826736711)
% 0.21/0.45  ipcrm: permission denied for id (826769480)
% 0.21/0.46  ipcrm: permission denied for id (826867787)
% 0.21/0.46  ipcrm: permission denied for id (824279119)
% 0.21/0.46  ipcrm: permission denied for id (824311889)
% 0.21/0.47  ipcrm: permission denied for id (827129941)
% 0.21/0.47  ipcrm: permission denied for id (827162710)
% 0.21/0.47  ipcrm: permission denied for id (827261017)
% 0.21/0.47  ipcrm: permission denied for id (827293786)
% 0.21/0.47  ipcrm: permission denied for id (827359324)
% 0.21/0.47  ipcrm: permission denied for id (824410205)
% 0.21/0.47  ipcrm: permission denied for id (827392094)
% 0.21/0.48  ipcrm: permission denied for id (827424863)
% 0.21/0.48  ipcrm: permission denied for id (824475744)
% 0.21/0.48  ipcrm: permission denied for id (827490402)
% 0.21/0.48  ipcrm: permission denied for id (827555940)
% 0.21/0.48  ipcrm: permission denied for id (827621478)
% 0.21/0.48  ipcrm: permission denied for id (827654247)
% 0.21/0.48  ipcrm: permission denied for id (827687016)
% 0.21/0.48  ipcrm: permission denied for id (827719785)
% 0.21/0.49  ipcrm: permission denied for id (827818092)
% 0.21/0.49  ipcrm: permission denied for id (827981937)
% 0.21/0.49  ipcrm: permission denied for id (828014706)
% 0.21/0.49  ipcrm: permission denied for id (828080244)
% 0.21/0.50  ipcrm: permission denied for id (824574069)
% 0.21/0.50  ipcrm: permission denied for id (828342397)
% 0.21/0.50  ipcrm: permission denied for id (828375166)
% 0.21/0.51  ipcrm: permission denied for id (824672383)
% 0.58/0.60  % (13914)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.58/0.61  % (13906)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.58/0.61  % (13904)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.58/0.61  % (13904)Refutation found. Thanks to Tanya!
% 0.58/0.61  % SZS status Theorem for theBenchmark
% 0.58/0.61  % SZS output start Proof for theBenchmark
% 0.58/0.61  fof(f152,plain,(
% 0.58/0.61    $false),
% 0.58/0.61    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f78,f84,f115,f118,f130,f141,f149,f151])).
% 0.58/0.61  fof(f151,plain,(
% 0.58/0.61    ~spl5_2 | ~spl5_11),
% 0.58/0.61    inference(avatar_contradiction_clause,[],[f150])).
% 0.58/0.61  fof(f150,plain,(
% 0.58/0.61    $false | (~spl5_2 | ~spl5_11)),
% 0.58/0.61    inference(subsumption_resolution,[],[f61,f126])).
% 0.58/0.61  fof(f126,plain,(
% 0.58/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_11),
% 0.58/0.61    inference(avatar_component_clause,[],[f125])).
% 0.58/0.61  fof(f125,plain,(
% 0.58/0.61    spl5_11 <=> ! [X1] : ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.58/0.61  fof(f61,plain,(
% 0.58/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 0.58/0.61    inference(avatar_component_clause,[],[f60])).
% 0.58/0.61  fof(f60,plain,(
% 0.58/0.61    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.58/0.61  fof(f149,plain,(
% 0.58/0.61    ~spl5_5 | ~spl5_4 | ~spl5_9 | ~spl5_6 | spl5_13),
% 0.58/0.61    inference(avatar_split_clause,[],[f145,f139,f76,f110,f68,f72])).
% 0.58/0.61  fof(f72,plain,(
% 0.58/0.61    spl5_5 <=> v2_pre_topc(sK0)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.58/0.61  fof(f68,plain,(
% 0.58/0.61    spl5_4 <=> l1_pre_topc(sK0)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.58/0.61  fof(f110,plain,(
% 0.58/0.61    spl5_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.58/0.61  fof(f76,plain,(
% 0.58/0.61    spl5_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.58/0.61  fof(f139,plain,(
% 0.58/0.61    spl5_13 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.58/0.61  fof(f145,plain,(
% 0.58/0.61    ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl5_13),
% 0.58/0.61    inference(resolution,[],[f140,f50])).
% 0.58/0.61  fof(f50,plain,(
% 0.58/0.61    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.58/0.61    inference(cnf_transformation,[],[f22])).
% 0.58/0.61  fof(f22,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.58/0.61    inference(flattening,[],[f21])).
% 0.58/0.61  fof(f21,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.58/0.61    inference(ennf_transformation,[],[f10])).
% 0.58/0.61  fof(f10,axiom,(
% 0.58/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.58/0.61  fof(f140,plain,(
% 0.58/0.61    ~v4_pre_topc(k1_xboole_0,sK0) | spl5_13),
% 0.58/0.61    inference(avatar_component_clause,[],[f139])).
% 0.58/0.61  fof(f141,plain,(
% 0.58/0.61    ~spl5_9 | ~spl5_13 | spl5_1 | ~spl5_7 | ~spl5_10 | ~spl5_12),
% 0.58/0.61    inference(avatar_split_clause,[],[f137,f128,f113,f82,f56,f139,f110])).
% 0.58/0.61  fof(f56,plain,(
% 0.58/0.61    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.58/0.61  fof(f82,plain,(
% 0.58/0.61    spl5_7 <=> k1_xboole_0 = sK1),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.58/0.61  fof(f113,plain,(
% 0.58/0.61    spl5_10 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.58/0.61  fof(f128,plain,(
% 0.58/0.61    spl5_12 <=> ! [X0] : (v2_tex_2(X0,sK0) | sK2(sK0,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0))),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.58/0.61  fof(f137,plain,(
% 0.58/0.61    ~v4_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_7 | ~spl5_10 | ~spl5_12)),
% 0.58/0.61    inference(forward_demodulation,[],[f136,f83])).
% 0.58/0.61  fof(f83,plain,(
% 0.58/0.61    k1_xboole_0 = sK1 | ~spl5_7),
% 0.58/0.61    inference(avatar_component_clause,[],[f82])).
% 0.58/0.61  fof(f136,plain,(
% 0.58/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (spl5_1 | ~spl5_7 | ~spl5_10 | ~spl5_12)),
% 0.58/0.61    inference(forward_demodulation,[],[f135,f83])).
% 0.58/0.61  fof(f135,plain,(
% 0.58/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (spl5_1 | ~spl5_7 | ~spl5_10 | ~spl5_12)),
% 0.58/0.61    inference(trivial_inequality_removal,[],[f134])).
% 0.58/0.61  fof(f134,plain,(
% 0.58/0.61    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (spl5_1 | ~spl5_7 | ~spl5_10 | ~spl5_12)),
% 0.58/0.61    inference(forward_demodulation,[],[f133,f114])).
% 0.58/0.61  fof(f114,plain,(
% 0.58/0.61    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl5_10),
% 0.58/0.61    inference(avatar_component_clause,[],[f113])).
% 0.58/0.61  fof(f133,plain,(
% 0.58/0.61    k1_xboole_0 != sK2(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (spl5_1 | ~spl5_7 | ~spl5_12)),
% 0.58/0.61    inference(forward_demodulation,[],[f131,f83])).
% 0.58/0.61  fof(f131,plain,(
% 0.58/0.61    sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (spl5_1 | ~spl5_12)),
% 0.58/0.61    inference(resolution,[],[f129,f57])).
% 0.58/0.61  fof(f57,plain,(
% 0.58/0.61    ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.58/0.61    inference(avatar_component_clause,[],[f56])).
% 0.58/0.61  fof(f129,plain,(
% 0.58/0.61    ( ! [X0] : (v2_tex_2(X0,sK0) | sK2(sK0,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl5_12),
% 0.58/0.61    inference(avatar_component_clause,[],[f128])).
% 0.58/0.61  fof(f130,plain,(
% 0.58/0.61    spl5_11 | spl5_12 | ~spl5_4),
% 0.58/0.61    inference(avatar_split_clause,[],[f123,f68,f128,f125])).
% 0.58/0.61  fof(f123,plain,(
% 0.58/0.61    ( ! [X0,X1] : (v2_tex_2(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X0) != X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_4),
% 0.58/0.61    inference(resolution,[],[f122,f69])).
% 0.58/0.61  fof(f69,plain,(
% 0.58/0.61    l1_pre_topc(sK0) | ~spl5_4),
% 0.58/0.61    inference(avatar_component_clause,[],[f68])).
% 0.58/0.61  fof(f122,plain,(
% 0.58/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sK2(X0,X1) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.58/0.61    inference(duplicate_literal_removal,[],[f121])).
% 0.58/0.61  fof(f121,plain,(
% 0.58/0.61    ( ! [X2,X0,X1] : (sK2(X0,X1) != X1 | v2_tex_2(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.58/0.61    inference(superposition,[],[f48,f54])).
% 0.58/0.61  fof(f54,plain,(
% 0.58/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.58/0.61    inference(cnf_transformation,[],[f24])).
% 0.58/0.61  fof(f24,plain,(
% 0.58/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.58/0.61    inference(ennf_transformation,[],[f7])).
% 0.58/0.61  fof(f7,axiom,(
% 0.58/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.58/0.61  fof(f48,plain,(
% 0.58/0.61    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.58/0.61    inference(cnf_transformation,[],[f32])).
% 0.58/0.61  fof(f32,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.58/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).
% 0.58/0.61  fof(f30,plain,(
% 0.58/0.61    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.58/0.61    introduced(choice_axiom,[])).
% 0.58/0.61  fof(f31,plain,(
% 0.58/0.61    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.58/0.61    introduced(choice_axiom,[])).
% 0.58/0.61  fof(f29,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.58/0.61    inference(rectify,[],[f28])).
% 0.58/0.61  fof(f28,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.58/0.61    inference(nnf_transformation,[],[f19])).
% 0.58/0.61  fof(f19,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.58/0.61    inference(flattening,[],[f18])).
% 0.58/0.61  fof(f18,plain,(
% 0.58/0.61    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.58/0.61    inference(ennf_transformation,[],[f11])).
% 0.58/0.61  fof(f11,axiom,(
% 0.58/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 0.58/0.61  fof(f118,plain,(
% 0.58/0.61    k1_xboole_0 != sK1 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.58/0.61    introduced(theory_tautology_sat_conflict,[])).
% 0.58/0.61  fof(f115,plain,(
% 0.58/0.61    ~spl5_9 | spl5_10 | spl5_1 | ~spl5_4 | ~spl5_7),
% 0.58/0.61    inference(avatar_split_clause,[],[f108,f82,f68,f56,f113,f110])).
% 0.58/0.61  fof(f108,plain,(
% 0.58/0.61    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_4 | ~spl5_7)),
% 0.58/0.61    inference(forward_demodulation,[],[f107,f92])).
% 0.58/0.61  fof(f92,plain,(
% 0.58/0.61    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.58/0.61    inference(resolution,[],[f53,f41])).
% 0.58/0.61  fof(f41,plain,(
% 0.58/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.58/0.61    inference(cnf_transformation,[],[f5])).
% 0.58/0.61  fof(f5,axiom,(
% 0.58/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.58/0.61  fof(f53,plain,(
% 0.58/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.58/0.61    inference(cnf_transformation,[],[f23])).
% 0.58/0.61  fof(f23,plain,(
% 0.58/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.58/0.61    inference(ennf_transformation,[],[f4])).
% 0.58/0.61  fof(f4,axiom,(
% 0.58/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.58/0.61  fof(f107,plain,(
% 0.58/0.61    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK2(sK0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_4 | ~spl5_7)),
% 0.58/0.61    inference(forward_demodulation,[],[f106,f83])).
% 0.58/0.61  fof(f106,plain,(
% 0.58/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_xboole_0(sK1,sK2(sK0,sK1)) | (spl5_1 | ~spl5_4 | ~spl5_7)),
% 0.58/0.61    inference(forward_demodulation,[],[f104,f83])).
% 0.58/0.61  fof(f104,plain,(
% 0.58/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_xboole_0(sK1,sK2(sK0,sK1)) | (spl5_1 | ~spl5_4)),
% 0.58/0.61    inference(resolution,[],[f103,f57])).
% 0.58/0.61  fof(f103,plain,(
% 0.58/0.61    ( ! [X0] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X0,sK2(sK0,X0)) = X0) ) | ~spl5_4),
% 0.58/0.61    inference(forward_demodulation,[],[f102,f52])).
% 0.58/0.61  fof(f52,plain,(
% 0.58/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.58/0.61    inference(cnf_transformation,[],[f1])).
% 0.58/0.61  fof(f1,axiom,(
% 0.58/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.58/0.61  fof(f102,plain,(
% 0.58/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | k2_xboole_0(sK2(sK0,X0),X0) = X0) ) | ~spl5_4),
% 0.58/0.61    inference(resolution,[],[f101,f53])).
% 0.58/0.61  fof(f101,plain,(
% 0.58/0.61    ( ! [X0] : (r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl5_4),
% 0.58/0.61    inference(resolution,[],[f47,f69])).
% 0.58/0.61  fof(f47,plain,(
% 0.58/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.58/0.61    inference(cnf_transformation,[],[f32])).
% 0.58/0.61  fof(f84,plain,(
% 0.58/0.61    spl5_7 | ~spl5_3),
% 0.58/0.61    inference(avatar_split_clause,[],[f79,f64,f82])).
% 0.58/0.61  fof(f64,plain,(
% 0.58/0.61    spl5_3 <=> v1_xboole_0(sK1)),
% 0.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.58/0.61  fof(f79,plain,(
% 0.58/0.61    k1_xboole_0 = sK1 | ~spl5_3),
% 0.58/0.61    inference(resolution,[],[f49,f65])).
% 0.58/0.61  % (13912)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.58/0.61  fof(f65,plain,(
% 0.58/0.61    v1_xboole_0(sK1) | ~spl5_3),
% 0.58/0.61    inference(avatar_component_clause,[],[f64])).
% 0.58/0.61  fof(f49,plain,(
% 0.58/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.58/0.61    inference(cnf_transformation,[],[f20])).
% 0.58/0.61  fof(f20,plain,(
% 0.58/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.58/0.61    inference(ennf_transformation,[],[f3])).
% 0.58/0.61  fof(f3,axiom,(
% 0.58/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.58/0.61  fof(f78,plain,(
% 0.58/0.61    spl5_6),
% 0.58/0.61    inference(avatar_split_clause,[],[f40,f76])).
% 0.58/0.61  fof(f40,plain,(
% 0.58/0.61    v1_xboole_0(k1_xboole_0)),
% 0.58/0.61    inference(cnf_transformation,[],[f2])).
% 0.58/0.61  fof(f2,axiom,(
% 0.58/0.61    v1_xboole_0(k1_xboole_0)),
% 0.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.58/0.61  fof(f74,plain,(
% 0.58/0.61    spl5_5),
% 0.58/0.61    inference(avatar_split_clause,[],[f35,f72])).
% 0.58/0.61  fof(f35,plain,(
% 0.58/0.61    v2_pre_topc(sK0)),
% 0.58/0.61    inference(cnf_transformation,[],[f27])).
% 0.58/0.61  fof(f27,plain,(
% 0.58/0.61    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.58/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f26,f25])).
% 0.58/0.61  fof(f25,plain,(
% 0.58/0.61    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.58/0.61    introduced(choice_axiom,[])).
% 0.58/0.61  fof(f26,plain,(
% 0.58/0.61    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1))),
% 0.58/0.61    introduced(choice_axiom,[])).
% 0.58/0.61  fof(f17,plain,(
% 0.58/0.61    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.58/0.61    inference(flattening,[],[f16])).
% 0.58/0.61  fof(f16,plain,(
% 0.58/0.61    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.58/0.61    inference(ennf_transformation,[],[f14])).
% 0.58/0.61  fof(f14,plain,(
% 0.58/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.58/0.61    inference(pure_predicate_removal,[],[f13])).
% 0.58/0.61  fof(f13,negated_conjecture,(
% 0.58/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.58/0.61    inference(negated_conjecture,[],[f12])).
% 0.58/0.62  fof(f12,conjecture,(
% 0.58/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.58/0.62  fof(f70,plain,(
% 0.58/0.62    spl5_4),
% 0.58/0.62    inference(avatar_split_clause,[],[f36,f68])).
% 0.58/0.62  fof(f36,plain,(
% 0.58/0.62    l1_pre_topc(sK0)),
% 0.58/0.62    inference(cnf_transformation,[],[f27])).
% 0.58/0.62  fof(f66,plain,(
% 0.58/0.62    spl5_3),
% 0.58/0.62    inference(avatar_split_clause,[],[f37,f64])).
% 0.58/0.62  fof(f37,plain,(
% 0.58/0.62    v1_xboole_0(sK1)),
% 0.58/0.62    inference(cnf_transformation,[],[f27])).
% 0.58/0.62  fof(f62,plain,(
% 0.58/0.62    spl5_2),
% 0.58/0.62    inference(avatar_split_clause,[],[f38,f60])).
% 0.58/0.62  fof(f38,plain,(
% 0.58/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.58/0.62    inference(cnf_transformation,[],[f27])).
% 0.58/0.62  fof(f58,plain,(
% 0.58/0.62    ~spl5_1),
% 0.58/0.62    inference(avatar_split_clause,[],[f39,f56])).
% 0.58/0.62  fof(f39,plain,(
% 0.58/0.62    ~v2_tex_2(sK1,sK0)),
% 0.58/0.62    inference(cnf_transformation,[],[f27])).
% 0.58/0.62  % SZS output end Proof for theBenchmark
% 0.58/0.62  % (13904)------------------------------
% 0.58/0.62  % (13904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.58/0.62  % (13904)Termination reason: Refutation
% 0.58/0.62  
% 0.58/0.62  % (13904)Memory used [KB]: 10618
% 0.58/0.62  % (13904)Time elapsed: 0.049 s
% 0.58/0.62  % (13904)------------------------------
% 0.58/0.62  % (13904)------------------------------
% 0.58/0.62  % (13764)Success in time 0.249 s
%------------------------------------------------------------------------------
