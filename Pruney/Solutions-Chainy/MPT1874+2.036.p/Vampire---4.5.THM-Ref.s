%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 222 expanded)
%              Number of leaves         :   33 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  384 (1004 expanded)
%              Number of equality atoms :   42 ( 135 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f104,f111,f116,f122,f132,f160,f167,f182,f184,f192,f212,f264])).

fof(f264,plain,
    ( spl5_28
    | ~ spl5_4
    | ~ spl5_20
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f249,f190,f80,f164,f75,f209])).

fof(f209,plain,
    ( spl5_28
  <=> k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f75,plain,
    ( spl5_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f164,plain,
    ( spl5_20
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f80,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f190,plain,
    ( spl5_24
  <=> ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k1_tarski(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f249,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ v2_tex_2(sK1,sK0)
    | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(resolution,[],[f191,f82])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tarski(sK2),X0)
        | ~ v2_tex_2(X0,sK0)
        | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k1_tarski(sK2))) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f190])).

fof(f212,plain,
    ( ~ spl5_28
    | spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f207,f129,f60,f209])).

fof(f60,plain,
    ( spl5_1
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f129,plain,
    ( spl5_14
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f207,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | spl5_1
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f62,f131])).

fof(f131,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f62,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f192,plain,
    ( spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f185,f179,f190,f85,f90,f95])).

fof(f95,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f90,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f85,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f179,plain,
    ( spl5_23
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK2),X0)
        | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k1_tarski(sK2)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_23 ),
    inference(resolution,[],[f181,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f181,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f179])).

fof(f184,plain,
    ( spl5_8
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f183,f125,f101,f95])).

fof(f101,plain,
    ( spl5_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f125,plain,
    ( spl5_13
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f183,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f127,f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f127,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f182,plain,
    ( spl5_13
    | ~ spl5_3
    | spl5_23
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f177,f129,f179,f70,f125])).

fof(f70,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f177,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(superposition,[],[f56,f131])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f167,plain,
    ( spl5_20
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f161,f157,f164])).

fof(f157,plain,
    ( spl5_19
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f161,plain,
    ( r1_tarski(k1_tarski(sK2),sK1)
    | ~ spl5_19 ),
    inference(resolution,[],[f159,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f159,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f157])).

fof(f160,plain,
    ( spl5_11
    | ~ spl5_10
    | spl5_19
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f155,f119,f157,f108,f113])).

fof(f113,plain,
    ( spl5_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f108,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f119,plain,
    ( spl5_12
  <=> k6_domain_1(sK1,sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f155,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_12 ),
    inference(superposition,[],[f56,f121])).

fof(f121,plain,
    ( k6_domain_1(sK1,sK2) = k1_tarski(sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f132,plain,
    ( spl5_13
    | spl5_14
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f123,f70,f129,f125])).

fof(f123,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f72,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f122,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f117,f108,f119,f113])).

fof(f117,plain,
    ( k6_domain_1(sK1,sK2) = k1_tarski(sK2)
    | v1_xboole_0(sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f110,f55])).

fof(f110,plain,
    ( m1_subset_1(sK2,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f116,plain,
    ( ~ spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f106,f65,f113])).

fof(f65,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f111,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f105,f65,f108])).

fof(f105,plain,
    ( m1_subset_1(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f104,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f99,f85,f101])).

fof(f99,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f98,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(f93,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f70])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f43,f65])).

fof(f43,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f60])).

fof(f44,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:16:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (800784385)
% 0.14/0.37  ipcrm: permission denied for id (801406978)
% 0.14/0.37  ipcrm: permission denied for id (800817155)
% 0.14/0.37  ipcrm: permission denied for id (800849924)
% 0.14/0.38  ipcrm: permission denied for id (801439749)
% 0.14/0.38  ipcrm: permission denied for id (801505287)
% 0.14/0.38  ipcrm: permission denied for id (801570825)
% 0.14/0.39  ipcrm: permission denied for id (800882702)
% 0.14/0.39  ipcrm: permission denied for id (801767440)
% 0.14/0.39  ipcrm: permission denied for id (800915473)
% 0.14/0.39  ipcrm: permission denied for id (801800210)
% 0.14/0.39  ipcrm: permission denied for id (801832979)
% 0.14/0.39  ipcrm: permission denied for id (801865748)
% 0.14/0.40  ipcrm: permission denied for id (801964055)
% 0.22/0.40  ipcrm: permission denied for id (801996824)
% 0.22/0.40  ipcrm: permission denied for id (802062362)
% 0.22/0.40  ipcrm: permission denied for id (800948251)
% 0.22/0.40  ipcrm: permission denied for id (802127901)
% 0.22/0.41  ipcrm: permission denied for id (802193439)
% 0.22/0.41  ipcrm: permission denied for id (802226208)
% 0.22/0.41  ipcrm: permission denied for id (802291746)
% 0.22/0.41  ipcrm: permission denied for id (801013795)
% 0.22/0.41  ipcrm: permission denied for id (802324516)
% 0.22/0.41  ipcrm: permission denied for id (802390054)
% 0.22/0.42  ipcrm: permission denied for id (802422823)
% 0.22/0.42  ipcrm: permission denied for id (802488361)
% 0.22/0.42  ipcrm: permission denied for id (802521130)
% 0.22/0.43  ipcrm: permission denied for id (802881589)
% 0.22/0.43  ipcrm: permission denied for id (802914358)
% 0.22/0.43  ipcrm: permission denied for id (802947127)
% 0.22/0.43  ipcrm: permission denied for id (802979896)
% 0.22/0.44  ipcrm: permission denied for id (803012665)
% 0.22/0.44  ipcrm: permission denied for id (801079358)
% 0.22/0.44  ipcrm: permission denied for id (803209279)
% 0.22/0.44  ipcrm: permission denied for id (803274817)
% 0.22/0.45  ipcrm: permission denied for id (803340355)
% 0.22/0.45  ipcrm: permission denied for id (803536969)
% 0.22/0.46  ipcrm: permission denied for id (803602507)
% 0.22/0.46  ipcrm: permission denied for id (803668045)
% 0.22/0.46  ipcrm: permission denied for id (803831890)
% 0.22/0.47  ipcrm: permission denied for id (801177684)
% 0.22/0.47  ipcrm: permission denied for id (803897429)
% 0.22/0.47  ipcrm: permission denied for id (803995736)
% 0.22/0.47  ipcrm: permission denied for id (804061274)
% 0.22/0.47  ipcrm: permission denied for id (804094043)
% 0.22/0.48  ipcrm: permission denied for id (804159581)
% 0.22/0.48  ipcrm: permission denied for id (804225119)
% 0.22/0.48  ipcrm: permission denied for id (804257888)
% 0.22/0.48  ipcrm: permission denied for id (804356195)
% 0.22/0.49  ipcrm: permission denied for id (804421733)
% 0.22/0.49  ipcrm: permission denied for id (804454502)
% 0.22/0.49  ipcrm: permission denied for id (804487271)
% 0.22/0.49  ipcrm: permission denied for id (804552809)
% 0.22/0.49  ipcrm: permission denied for id (804683884)
% 0.22/0.50  ipcrm: permission denied for id (804782191)
% 0.22/0.50  ipcrm: permission denied for id (804814960)
% 0.22/0.50  ipcrm: permission denied for id (804913267)
% 0.22/0.50  ipcrm: permission denied for id (804946036)
% 0.22/0.51  ipcrm: permission denied for id (805044342)
% 0.22/0.51  ipcrm: permission denied for id (805077111)
% 0.22/0.51  ipcrm: permission denied for id (805208187)
% 0.22/0.51  ipcrm: permission denied for id (805273725)
% 0.22/0.57  % (5023)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.58  % (5023)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f269,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f88,f93,f98,f104,f111,f116,f122,f132,f160,f167,f182,f184,f192,f212,f264])).
% 0.22/0.58  fof(f264,plain,(
% 0.22/0.58    spl5_28 | ~spl5_4 | ~spl5_20 | ~spl5_5 | ~spl5_24),
% 0.22/0.58    inference(avatar_split_clause,[],[f249,f190,f80,f164,f75,f209])).
% 0.22/0.58  fof(f209,plain,(
% 0.22/0.58    spl5_28 <=> k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    spl5_4 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.58  fof(f164,plain,(
% 0.22/0.58    spl5_20 <=> r1_tarski(k1_tarski(sK2),sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    spl5_24 <=> ! [X0] : (~r1_tarski(k1_tarski(sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k1_tarski(sK2))))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.58  fof(f249,plain,(
% 0.22/0.58    ~r1_tarski(k1_tarski(sK2),sK1) | ~v2_tex_2(sK1,sK0) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | (~spl5_5 | ~spl5_24)),
% 0.22/0.58    inference(resolution,[],[f191,f82])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f80])).
% 0.22/0.58  fof(f191,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),X0) | ~v2_tex_2(X0,sK0) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k1_tarski(sK2)))) ) | ~spl5_24),
% 0.22/0.58    inference(avatar_component_clause,[],[f190])).
% 0.22/0.58  fof(f212,plain,(
% 0.22/0.58    ~spl5_28 | spl5_1 | ~spl5_14),
% 0.22/0.58    inference(avatar_split_clause,[],[f207,f129,f60,f209])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    spl5_1 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    spl5_14 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.58  fof(f207,plain,(
% 0.22/0.58    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | (spl5_1 | ~spl5_14)),
% 0.22/0.58    inference(forward_demodulation,[],[f62,f131])).
% 0.22/0.58  fof(f131,plain,(
% 0.22/0.58    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~spl5_14),
% 0.22/0.58    inference(avatar_component_clause,[],[f129])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f60])).
% 0.22/0.58  fof(f192,plain,(
% 0.22/0.58    spl5_8 | ~spl5_7 | ~spl5_6 | spl5_24 | ~spl5_23),
% 0.22/0.58    inference(avatar_split_clause,[],[f185,f179,f190,f85,f90,f95])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    spl5_8 <=> v2_struct_0(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    spl5_7 <=> v2_pre_topc(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    spl5_6 <=> l1_pre_topc(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    spl5_23 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.58  fof(f185,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(k1_tarski(sK2),X0) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k1_tarski(sK2))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_23),
% 0.22/0.58    inference(resolution,[],[f181,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(rectify,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_23),
% 0.22/0.58    inference(avatar_component_clause,[],[f179])).
% 0.22/0.58  fof(f184,plain,(
% 0.22/0.58    spl5_8 | ~spl5_9 | ~spl5_13),
% 0.22/0.58    inference(avatar_split_clause,[],[f183,f125,f101,f95])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    spl5_9 <=> l1_struct_0(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    spl5_13 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.58  fof(f183,plain,(
% 0.22/0.58    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_13),
% 0.22/0.58    inference(resolution,[],[f127,f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f125])).
% 0.22/0.58  fof(f182,plain,(
% 0.22/0.58    spl5_13 | ~spl5_3 | spl5_23 | ~spl5_14),
% 0.22/0.58    inference(avatar_split_clause,[],[f177,f129,f179,f70,f125])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_14),
% 0.22/0.58    inference(superposition,[],[f56,f131])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.58  fof(f167,plain,(
% 0.22/0.58    spl5_20 | ~spl5_19),
% 0.22/0.58    inference(avatar_split_clause,[],[f161,f157,f164])).
% 0.22/0.58  fof(f157,plain,(
% 0.22/0.58    spl5_19 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    r1_tarski(k1_tarski(sK2),sK1) | ~spl5_19),
% 0.22/0.58    inference(resolution,[],[f159,f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1)) | ~spl5_19),
% 0.22/0.58    inference(avatar_component_clause,[],[f157])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    spl5_11 | ~spl5_10 | spl5_19 | ~spl5_12),
% 0.22/0.58    inference(avatar_split_clause,[],[f155,f119,f157,f108,f113])).
% 0.22/0.58  fof(f113,plain,(
% 0.22/0.58    spl5_11 <=> v1_xboole_0(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.58  fof(f108,plain,(
% 0.22/0.58    spl5_10 <=> m1_subset_1(sK2,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    spl5_12 <=> k6_domain_1(sK1,sK2) = k1_tarski(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,sK1) | v1_xboole_0(sK1) | ~spl5_12),
% 0.22/0.58    inference(superposition,[],[f56,f121])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    k6_domain_1(sK1,sK2) = k1_tarski(sK2) | ~spl5_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f119])).
% 0.22/0.58  fof(f132,plain,(
% 0.22/0.58    spl5_13 | spl5_14 | ~spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f123,f70,f129,f125])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_3),
% 0.22/0.58    inference(resolution,[],[f72,f55])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f70])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    spl5_11 | spl5_12 | ~spl5_10),
% 0.22/0.58    inference(avatar_split_clause,[],[f117,f108,f119,f113])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    k6_domain_1(sK1,sK2) = k1_tarski(sK2) | v1_xboole_0(sK1) | ~spl5_10),
% 0.22/0.58    inference(resolution,[],[f110,f55])).
% 0.22/0.58  fof(f110,plain,(
% 0.22/0.58    m1_subset_1(sK2,sK1) | ~spl5_10),
% 0.22/0.58    inference(avatar_component_clause,[],[f108])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    ~spl5_11 | ~spl5_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f106,f65,f113])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    ~v1_xboole_0(sK1) | ~spl5_2),
% 0.22/0.58    inference(resolution,[],[f67,f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.58    inference(rectify,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    r2_hidden(sK2,sK1) | ~spl5_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f65])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    spl5_10 | ~spl5_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f105,f65,f108])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    m1_subset_1(sK2,sK1) | ~spl5_2),
% 0.22/0.58    inference(resolution,[],[f67,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    spl5_9 | ~spl5_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f99,f85,f101])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    l1_struct_0(sK0) | ~spl5_6),
% 0.22/0.58    inference(resolution,[],[f87,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    l1_pre_topc(sK0) | ~spl5_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f85])).
% 0.22/0.58  fof(f98,plain,(
% 0.22/0.58    ~spl5_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f37,f95])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ~v2_struct_0(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,negated_conjecture,(
% 0.22/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.58    inference(negated_conjecture,[],[f10])).
% 0.22/0.58  fof(f10,conjecture,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    spl5_7),
% 0.22/0.58    inference(avatar_split_clause,[],[f38,f90])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    v2_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f88,plain,(
% 0.22/0.58    spl5_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f39,f85])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    l1_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    spl5_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f40,f80])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    spl5_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f41,f75])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    v2_tex_2(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    spl5_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f42,f70])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    spl5_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f43,f65])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    r2_hidden(sK2,sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ~spl5_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f44,f60])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (5023)------------------------------
% 0.22/0.58  % (5023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (5023)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (5023)Memory used [KB]: 10746
% 0.22/0.58  % (5023)Time elapsed: 0.009 s
% 0.22/0.58  % (5023)------------------------------
% 0.22/0.58  % (5023)------------------------------
% 0.22/0.58  % (4877)Success in time 0.214 s
%------------------------------------------------------------------------------
