%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 317 expanded)
%              Number of leaves         :   35 ( 130 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 (2421 expanded)
%              Number of equality atoms :   29 ( 195 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f112,f119,f129,f142,f163,f177,f187,f196,f203,f221,f233])).

fof(f233,plain,
    ( ~ spl4_20
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f223,f147,f138,f218])).

fof(f218,plain,
    ( spl4_20
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f138,plain,
    ( spl4_9
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f147,plain,
    ( spl4_10
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f223,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f120,f140,f113,f149,f54])).

fof(f54,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f149,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f82,f80])).

fof(f80,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f77,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f76,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f58,f55])).

fof(f55,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f140,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f79,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f221,plain,
    ( spl4_20
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f216,f200,f94,f218])).

fof(f94,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f200,plain,
    ( spl4_17
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f216,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f208,f80])).

fof(f208,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f96,f202,f81,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f202,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f96,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f203,plain,
    ( spl4_17
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f197,f109,f99,f94,f200])).

fof(f99,plain,
    ( spl4_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f109,plain,
    ( spl4_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f197,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f101,f96,f111,f81,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f111,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f196,plain,
    ( spl4_10
    | ~ spl4_2
    | spl4_11 ),
    inference(avatar_split_clause,[],[f188,f151,f89,f147])).

fof(f89,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f151,plain,
    ( spl4_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f188,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f91,f152,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f152,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f91,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f187,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f185,f104,f99,f94,f174])).

fof(f174,plain,
    ( spl4_14
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f104,plain,
    ( spl4_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f185,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f106,f101,f96,f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f177,plain,
    ( ~ spl4_14
    | ~ spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f171,f160,f151,f174])).

fof(f160,plain,
    ( spl4_12
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f171,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f153,f162,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f162,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f153,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f163,plain,
    ( ~ spl4_12
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f158,f104,f99,f94,f160])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f106,f101,f96,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f135,f125,f138,f94,f99])).

fof(f125,plain,
    ( spl4_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f135,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(superposition,[],[f71,f127])).

fof(f127,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f71,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f129,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f123,f116,f125])).

fof(f116,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f123,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f63,f118])).

fof(f118,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f119,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f114,f94,f116])).

fof(f114,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f96,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f112,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f78,f109])).

fof(f78,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f107,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f46,f104])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f47,f99])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f48,f94])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (30759)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.42  % (30759)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f235,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f112,f119,f129,f142,f163,f177,f187,f196,f203,f221,f233])).
% 0.21/0.42  fof(f233,plain,(
% 0.21/0.42    ~spl4_20 | ~spl4_9 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f223,f147,f138,f218])).
% 0.21/0.42  fof(f218,plain,(
% 0.21/0.42    spl4_20 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    spl4_9 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    spl4_10 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f223,plain,(
% 0.21/0.42    ~v3_pre_topc(u1_struct_0(sK0),sK0) | (~spl4_9 | ~spl4_10)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f120,f140,f113,f149,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.42    inference(negated_conjecture,[],[f18])).
% 0.21/0.42  fof(f18,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f147])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f82,f80])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.21/0.42    inference(definition_unfolding,[],[f59,f77])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f62,f76])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.21/0.42    inference(definition_unfolding,[],[f58,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    k1_xboole_0 = sK2),
% 0.21/0.42    inference(cnf_transformation,[],[f42])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f61,f77])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    v4_pre_topc(u1_struct_0(sK0),sK0) | ~spl4_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f138])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f79,f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f57,f55])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.42  fof(f221,plain,(
% 0.21/0.42    spl4_20 | ~spl4_3 | ~spl4_17),
% 0.21/0.42    inference(avatar_split_clause,[],[f216,f200,f94,f218])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl4_3 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f200,plain,(
% 0.21/0.42    spl4_17 <=> v4_pre_topc(sK2,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.42  fof(f216,plain,(
% 0.21/0.42    v3_pre_topc(u1_struct_0(sK0),sK0) | (~spl4_3 | ~spl4_17)),
% 0.21/0.42    inference(forward_demodulation,[],[f208,f80])).
% 0.21/0.42  fof(f208,plain,(
% 0.21/0.42    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | (~spl4_3 | ~spl4_17)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f96,f202,f81,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f60,f55])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.42  fof(f202,plain,(
% 0.21/0.42    v4_pre_topc(sK2,sK0) | ~spl4_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f200])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f94])).
% 0.21/0.42  fof(f203,plain,(
% 0.21/0.42    spl4_17 | ~spl4_3 | ~spl4_4 | ~spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f197,f109,f99,f94,f200])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl4_4 <=> v2_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    spl4_6 <=> v1_xboole_0(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f197,plain,(
% 0.21/0.42    v4_pre_topc(sK2,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_6)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f101,f96,f111,f81,f72])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,axiom,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    v1_xboole_0(sK2) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f109])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    v2_pre_topc(sK0) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f99])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    spl4_10 | ~spl4_2 | spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f188,f151,f89,f147])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl4_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    spl4_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f188,plain,(
% 0.21/0.42    r2_hidden(sK1,u1_struct_0(sK0)) | (~spl4_2 | spl4_11)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f91,f152,f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f151])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f187,plain,(
% 0.21/0.42    spl4_14 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f185,f104,f99,f94,f174])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    spl4_14 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    spl4_5 <=> v2_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f185,plain,(
% 0.21/0.42    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f106,f101,f96,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,axiom,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ~v2_struct_0(sK0) | spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f104])).
% 0.21/0.42  fof(f177,plain,(
% 0.21/0.42    ~spl4_14 | ~spl4_11 | spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f171,f160,f151,f174])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    spl4_12 <=> v1_xboole_0(sK3(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    ~m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_11 | spl4_12)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f153,f162,f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.42  fof(f162,plain,(
% 0.21/0.42    ~v1_xboole_0(sK3(sK0)) | spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f160])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f151])).
% 0.21/0.42  fof(f163,plain,(
% 0.21/0.42    ~spl4_12 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f158,f104,f99,f94,f160])).
% 0.21/0.42  fof(f158,plain,(
% 0.21/0.42    ~v1_xboole_0(sK3(sK0)) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f106,f101,f96,f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f45])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    ~spl4_4 | ~spl4_3 | spl4_9 | ~spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f135,f125,f138,f94,f99])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    spl4_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    v4_pre_topc(u1_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_8),
% 0.21/0.42    inference(superposition,[],[f71,f127])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f125])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,axiom,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    spl4_8 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f123,f116,f125])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl4_7 <=> l1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_7),
% 0.21/0.42    inference(resolution,[],[f63,f118])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f116])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl4_7 | ~spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f114,f94,f116])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl4_3),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f96,f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f78,f109])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    v1_xboole_0(sK2)),
% 0.21/0.42    inference(definition_unfolding,[],[f56,f55])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    ~spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f46,f104])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ~v2_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f42])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f47,f99])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    v2_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f42])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f48,f94])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    l1_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f42])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f49,f89])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f42])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (30759)------------------------------
% 0.21/0.42  % (30759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (30759)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (30759)Memory used [KB]: 6268
% 0.21/0.42  % (30759)Time elapsed: 0.010 s
% 0.21/0.42  % (30759)------------------------------
% 0.21/0.42  % (30759)------------------------------
% 0.21/0.42  % (30752)Success in time 0.066 s
%------------------------------------------------------------------------------
