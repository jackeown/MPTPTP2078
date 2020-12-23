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
% DateTime   : Thu Dec  3 13:15:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 208 expanded)
%              Number of leaves         :   28 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  449 (1366 expanded)
%              Number of equality atoms :   28 ( 104 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f90,f104,f109,f122,f167,f187,f192,f198,f204,f213])).

fof(f213,plain,(
    ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f210,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f210,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_21 ),
    inference(resolution,[],[f186,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f186,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_21
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f204,plain,
    ( ~ spl3_9
    | spl3_11
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl3_9
    | spl3_11
    | spl3_20 ),
    inference(subsumption_resolution,[],[f202,f108])).

fof(f108,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_9
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_11
    | spl3_20 ),
    inference(subsumption_resolution,[],[f200,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_11
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f200,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_20 ),
    inference(resolution,[],[f182,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f182,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_20
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f198,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_19 ),
    inference(subsumption_resolution,[],[f196,f68])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f196,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | spl3_19 ),
    inference(subsumption_resolution,[],[f194,f73])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f194,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_19 ),
    inference(resolution,[],[f178,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f178,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_19
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f192,plain,(
    spl3_18 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl3_18 ),
    inference(subsumption_resolution,[],[f189,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f189,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_18 ),
    inference(resolution,[],[f174,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f174,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_18
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f187,plain,
    ( ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20
    | spl3_21
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f170,f165,f71,f66,f184,f180,f176,f172])).

fof(f165,plain,
    ( spl3_17
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f170,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f168,f73])).

fof(f168,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_17 ),
    inference(resolution,[],[f166,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f166,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f163,f101,f76,f165])).

fof(f76,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f101,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f163,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f162,f103])).

fof(f103,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f162,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f43,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f43,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f122,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f117,f101,f87,f61,f119])).

fof(f61,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f116,f63])).

fof(f63,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f116,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f115,f89])).

fof(f89,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f115,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(superposition,[],[f48,f103])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f109,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f99,f87,f81,f106])).

fof(f81,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f99,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f83,f97])).

fof(f97,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f46,f89])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f83,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f104,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f97,f87,f101])).

fof(f90,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f85,f71,f87])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f47,f73])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f84,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (17552)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.48  % (17543)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (17543)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f90,f104,f109,f122,f167,f187,f192,f198,f204,f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    ~spl3_21),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f212])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    $false | ~spl3_21),
% 0.20/0.49    inference(subsumption_resolution,[],[f210,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~r1_tarski(k1_xboole_0,k2_struct_0(sK0)) | ~spl3_21),
% 0.20/0.49    inference(resolution,[],[f186,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f184])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl3_21 <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ~spl3_9 | spl3_11 | spl3_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    $false | (~spl3_9 | spl3_11 | spl3_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f202,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl3_9 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k2_struct_0(sK0)) | (spl3_11 | spl3_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f200,f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl3_11 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl3_20),
% 0.20/0.49    inference(resolution,[],[f182,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl3_20 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    ~spl3_2 | ~spl3_3 | spl3_19),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    $false | (~spl3_2 | ~spl3_3 | spl3_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f196,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v2_pre_topc(sK0) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_2 <=> v2_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | (~spl3_3 | spl3_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f194,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl3_3 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_19),
% 0.20/0.49    inference(resolution,[],[f178,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f176])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    spl3_19 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    spl3_18),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f191])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    $false | spl3_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f189,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl3_18),
% 0.20/0.49    inference(resolution,[],[f174,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f172])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    spl3_18 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    ~spl3_18 | ~spl3_19 | ~spl3_20 | spl3_21 | ~spl3_2 | ~spl3_3 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f170,f165,f71,f66,f184,f180,f176,f172])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl3_17 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | ~spl3_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f68])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f73])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_17),
% 0.20/0.49    inference(resolution,[],[f166,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X3] : (~v3_pre_topc(X3,sK0) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f165])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl3_17 | ~spl3_4 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f163,f101,f76,f165])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_4 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | (~spl3_4 | ~spl3_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f162,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.20/0.49    inference(forward_demodulation,[],[f43,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ~spl3_11 | spl3_1 | ~spl3_6 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f117,f101,f87,f61,f119])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl3_6 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | (spl3_1 | ~spl3_6 | ~spl3_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_6 | ~spl3_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    l1_struct_0(sK0) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_8),
% 0.20/0.49    inference(superposition,[],[f48,f103])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl3_9 | ~spl3_5 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f87,f81,f106])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_5 | ~spl3_6)),
% 0.20/0.49    inference(backward_demodulation,[],[f83,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 0.20/0.49    inference(resolution,[],[f46,f89])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl3_8 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f97,f87,f101])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl3_6 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f85,f71,f87])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    l1_struct_0(sK0) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f47,f73])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f81])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f76])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    k1_xboole_0 = sK2),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f71])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f66])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f61])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (17543)------------------------------
% 0.20/0.49  % (17543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17543)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (17543)Memory used [KB]: 6268
% 0.20/0.49  % (17543)Time elapsed: 0.066 s
% 0.20/0.49  % (17543)------------------------------
% 0.20/0.49  % (17543)------------------------------
% 0.20/0.49  % (17538)Success in time 0.126 s
%------------------------------------------------------------------------------
