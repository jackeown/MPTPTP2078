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
% DateTime   : Thu Dec  3 13:15:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 450 expanded)
%              Number of leaves         :   44 ( 179 expanded)
%              Depth                    :   15
%              Number of atoms          :  538 (3392 expanded)
%              Number of equality atoms :   49 ( 321 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1005,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f116,f122,f129,f135,f143,f149,f155,f162,f185,f272,f335,f417,f502,f508,f698,f1001,f1004])).

fof(f1004,plain,
    ( sK2 != sK3(sK0)
    | sK2 != k2_struct_0(sK0)
    | v2_tops_1(k2_struct_0(sK0),sK0)
    | ~ v2_tops_1(sK3(sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1001,plain,
    ( spl5_68
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f700,f696,f998])).

fof(f998,plain,
    ( spl5_68
  <=> sK2 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f696,plain,
    ( spl5_58
  <=> ! [X0] : ~ r2_hidden(X0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f700,plain,
    ( sK2 = sK3(sK0)
    | ~ spl5_58 ),
    inference(resolution,[],[f697,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f71,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK4(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK4(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f697,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(sK0))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f696])).

fof(f698,plain,
    ( spl5_58
    | ~ spl5_10
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f524,f319,f140,f696])).

fof(f140,plain,
    ( spl5_10
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f319,plain,
    ( spl5_31
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f524,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(sK0))
    | ~ spl5_10
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f142,f320,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f320,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f319])).

fof(f142,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f508,plain,(
    spl5_43 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f84,f501])).

fof(f501,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl5_43
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f80,f78])).

fof(f78,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f75,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f502,plain,
    ( ~ spl5_43
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f433,f265,f160,f152,f146,f126,f499])).

fof(f126,plain,
    ( spl5_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f146,plain,
    ( spl5_11
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f152,plain,
    ( spl5_12
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f160,plain,
    ( spl5_13
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f265,plain,
    ( spl5_26
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f433,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f425,f128])).

fof(f128,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f425,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f161,f154,f148,f267,f55])).

fof(f55,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f267,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f265])).

fof(f148,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f154,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f161,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f417,plain,(
    ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl5_27 ),
    inference(global_subsumption,[],[f77,f388])).

fof(f388,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f84,f271,f74])).

fof(f271,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl5_27
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f77,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f335,plain,
    ( sK2 != k2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v1_xboole_0(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f272,plain,
    ( spl5_25
    | spl5_26
    | spl5_27
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f233,f132,f269,f265,f261])).

fof(f261,plain,
    ( spl5_25
  <=> sK2 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f132,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f233,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k2_struct_0(sK0))
    | sK2 = k2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f226,f134])).

fof(f134,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,sK2)
      | r2_hidden(X1,X0)
      | sK2 = X0 ) ),
    inference(global_subsumption,[],[f79,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(superposition,[],[f81,f78])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f67,f56])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f185,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f180,f96,f91,f86,f182])).

fof(f182,plain,
    ( spl5_16
  <=> v2_tops_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f86,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f91,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f180,plain,
    ( ~ v2_tops_1(k2_struct_0(sK0),sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f162,plain,
    ( spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f157,f101,f160])).

fof(f101,plain,
    ( spl5_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f157,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f103,f84,f74])).

fof(f103,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f155,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f150,f96,f91,f152])).

fof(f150,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f93,f98,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f149,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f144,f96,f91,f146])).

fof(f144,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f93,f98,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f143,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f138,f126,f96,f140])).

fof(f138,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f136,f128])).

fof(f136,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_tops_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v2_tops_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

fof(f135,plain,
    ( spl5_9
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f130,f126,f106,f132])).

fof(f106,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f130,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(superposition,[],[f108,f128])).

fof(f108,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f129,plain,
    ( spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f123,f113,f126])).

fof(f113,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f123,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f115,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f115,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f122,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f117,f96,f119])).

fof(f119,plain,
    ( spl5_7
  <=> v2_tops_1(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f117,plain,
    ( v2_tops_1(sK3(sK0),sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v2_tops_1(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f110,f96,f113])).

fof(f110,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f109,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f77,f101])).

fof(f99,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f47,f86])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (3495)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.43  % (3495)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f1005,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f116,f122,f129,f135,f143,f149,f155,f162,f185,f272,f335,f417,f502,f508,f698,f1001,f1004])).
% 0.21/0.43  fof(f1004,plain,(
% 0.21/0.43    sK2 != sK3(sK0) | sK2 != k2_struct_0(sK0) | v2_tops_1(k2_struct_0(sK0),sK0) | ~v2_tops_1(sK3(sK0),sK0)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f1001,plain,(
% 0.21/0.43    spl5_68 | ~spl5_58),
% 0.21/0.43    inference(avatar_split_clause,[],[f700,f696,f998])).
% 0.21/0.43  fof(f998,plain,(
% 0.21/0.43    spl5_68 <=> sK2 = sK3(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.21/0.43  fof(f696,plain,(
% 0.21/0.43    spl5_58 <=> ! [X0] : ~r2_hidden(X0,sK3(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.21/0.43  fof(f700,plain,(
% 0.21/0.43    sK2 = sK3(sK0) | ~spl5_58),
% 0.21/0.43    inference(resolution,[],[f697,f83])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK4(X0),X0) | sK2 = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f71,f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    k1_xboole_0 = sK2),
% 0.21/0.43    inference(cnf_transformation,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f17])).
% 0.21/0.43  fof(f17,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK4(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK4(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK4(X0),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(flattening,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.43  fof(f697,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,sK3(sK0))) ) | ~spl5_58),
% 0.21/0.43    inference(avatar_component_clause,[],[f696])).
% 0.21/0.43  fof(f698,plain,(
% 0.21/0.43    spl5_58 | ~spl5_10 | ~spl5_31),
% 0.21/0.43    inference(avatar_split_clause,[],[f524,f319,f140,f696])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    spl5_10 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.43  fof(f319,plain,(
% 0.21/0.43    spl5_31 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.43  fof(f524,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,sK3(sK0))) ) | (~spl5_10 | ~spl5_31)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f142,f320,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.43  fof(f320,plain,(
% 0.21/0.43    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_31),
% 0.21/0.43    inference(avatar_component_clause,[],[f319])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f140])).
% 0.21/0.43  fof(f508,plain,(
% 0.21/0.43    spl5_43),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f503])).
% 0.21/0.43  fof(f503,plain,(
% 0.21/0.43    $false | spl5_43),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f84,f501])).
% 0.21/0.43  fof(f501,plain,(
% 0.21/0.43    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_43),
% 0.21/0.43    inference(avatar_component_clause,[],[f499])).
% 0.21/0.43  fof(f499,plain,(
% 0.21/0.43    spl5_43 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f80,f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f59,f76])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f62,f75])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.21/0.43    inference(definition_unfolding,[],[f58,f56])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f61,f76])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.43  fof(f502,plain,(
% 0.21/0.43    ~spl5_43 | ~spl5_8 | ~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_26),
% 0.21/0.43    inference(avatar_split_clause,[],[f433,f265,f160,f152,f146,f126,f499])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    spl5_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    spl5_11 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.43  fof(f152,plain,(
% 0.21/0.43    spl5_12 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.43  fof(f160,plain,(
% 0.21/0.43    spl5_13 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.43  fof(f265,plain,(
% 0.21/0.43    spl5_26 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.43  fof(f433,plain,(
% 0.21/0.43    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_8 | ~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_26)),
% 0.21/0.43    inference(forward_demodulation,[],[f425,f128])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f126])).
% 0.21/0.43  fof(f425,plain,(
% 0.21/0.43    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_26)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f161,f154,f148,f267,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X3] : (~r2_hidden(sK1,X3) | r2_hidden(X3,sK2) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f42])).
% 0.21/0.43  fof(f267,plain,(
% 0.21/0.43    r2_hidden(sK1,k2_struct_0(sK0)) | ~spl5_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f265])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    v4_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f146])).
% 0.21/0.43  fof(f154,plain,(
% 0.21/0.43    v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f152])).
% 0.21/0.43  fof(f161,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f160])).
% 0.21/0.43  fof(f417,plain,(
% 0.21/0.43    ~spl5_27),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f416])).
% 0.21/0.43  fof(f416,plain,(
% 0.21/0.43    $false | ~spl5_27),
% 0.21/0.43    inference(global_subsumption,[],[f77,f388])).
% 0.21/0.43  fof(f388,plain,(
% 0.21/0.43    ~v1_xboole_0(sK2) | ~spl5_27),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f84,f271,f74])).
% 0.21/0.43  fof(f271,plain,(
% 0.21/0.43    r2_hidden(sK1,sK2) | ~spl5_27),
% 0.21/0.43    inference(avatar_component_clause,[],[f269])).
% 0.21/0.43  fof(f269,plain,(
% 0.21/0.43    spl5_27 <=> r2_hidden(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    v1_xboole_0(sK2)),
% 0.21/0.43    inference(definition_unfolding,[],[f57,f56])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f335,plain,(
% 0.21/0.43    sK2 != k2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~v1_xboole_0(sK2)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f272,plain,(
% 0.21/0.43    spl5_25 | spl5_26 | spl5_27 | ~spl5_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f233,f132,f269,f265,f261])).
% 0.21/0.43  fof(f261,plain,(
% 0.21/0.43    spl5_25 <=> sK2 = k2_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    spl5_9 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.43  fof(f233,plain,(
% 0.21/0.43    r2_hidden(sK1,sK2) | r2_hidden(sK1,k2_struct_0(sK0)) | sK2 = k2_struct_0(sK0) | ~spl5_9),
% 0.21/0.43    inference(resolution,[],[f226,f134])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl5_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f132])).
% 0.21/0.43  fof(f226,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,sK2) | r2_hidden(X1,X0) | sK2 = X0) )),
% 0.21/0.43    inference(global_subsumption,[],[f79,f223])).
% 0.21/0.43  fof(f223,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,sK2) | ~m1_subset_1(X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 0.21/0.43    inference(superposition,[],[f81,f78])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f67,f56])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(flattening,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f60,f56])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.43  fof(f185,plain,(
% 0.21/0.43    ~spl5_16 | spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f180,f96,f91,f86,f182])).
% 0.21/0.43  fof(f182,plain,(
% 0.21/0.43    spl5_16 <=> v2_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl5_2 <=> v2_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    spl5_3 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    ~v2_tops_1(k2_struct_0(sK0),sK0) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f88,f93,f98,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_tops_1(k2_struct_0(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl5_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f96])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    v2_pre_topc(sK0) | ~spl5_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f91])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f86])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    spl5_13 | ~spl5_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f157,f101,f160])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl5_4 <=> v1_xboole_0(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_4),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f103,f84,f74])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    v1_xboole_0(sK2) | ~spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f101])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl5_12 | ~spl5_2 | ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f150,f96,f91,f152])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl5_2 | ~spl5_3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f93,f98,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl5_11 | ~spl5_2 | ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f144,f96,f91,f146])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    v4_pre_topc(k2_struct_0(sK0),sK0) | (~spl5_2 | ~spl5_3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f93,f98,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    spl5_10 | ~spl5_3 | ~spl5_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f138,f126,f96,f140])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_3 | ~spl5_8)),
% 0.21/0.44    inference(forward_demodulation,[],[f136,f128])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f98,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ! [X0] : ((v2_tops_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    spl5_9 | ~spl5_5 | ~spl5_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f130,f126,f106,f132])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl5_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl5_5 | ~spl5_8)),
% 0.21/0.44    inference(superposition,[],[f108,f128])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    spl5_8 | ~spl5_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f123,f113,f126])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    spl5_6 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_6),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f115,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl5_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f113])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    spl5_7 | ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f117,f96,f119])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    spl5_7 <=> v2_tops_1(sK3(sK0),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    v2_tops_1(sK3(sK0),sK0) | ~spl5_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f98,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X0] : (v2_tops_1(sK3(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f44])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl5_6 | ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f110,f96,f113])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl5_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f98,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl5_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f50,f106])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl5_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f77,f101])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f96])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl5_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f91])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ~spl5_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f47,f86])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f42])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (3495)------------------------------
% 0.21/0.44  % (3495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (3495)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (3495)Memory used [KB]: 11257
% 0.21/0.44  % (3495)Time elapsed: 0.025 s
% 0.21/0.44  % (3495)------------------------------
% 0.21/0.44  % (3495)------------------------------
% 0.21/0.44  % (3477)Success in time 0.088 s
%------------------------------------------------------------------------------
