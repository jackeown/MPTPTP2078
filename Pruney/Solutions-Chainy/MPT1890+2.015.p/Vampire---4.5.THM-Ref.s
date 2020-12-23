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
% DateTime   : Thu Dec  3 13:22:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 282 expanded)
%              Number of leaves         :   34 ( 136 expanded)
%              Depth                    :    9
%              Number of atoms          :  524 (1289 expanded)
%              Number of equality atoms :   37 ( 116 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f119,f126,f136,f154,f164,f169,f176,f184,f211,f217,f229,f266,f280,f285,f346])).

fof(f346,plain,
    ( ~ spl5_27
    | spl5_1
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_33
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f327,f282,f277,f264,f133,f67,f62,f219])).

fof(f219,plain,
    ( spl5_27
  <=> k1_tarski(sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f62,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f67,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f133,plain,
    ( spl5_14
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f264,plain,
    ( spl5_33
  <=> ! [X1,X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,X1) != k1_tarski(sK2(sK0,X0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f277,plain,
    ( spl5_35
  <=> v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f282,plain,
    ( spl5_36
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f327,plain,
    ( k1_tarski(sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_33
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f64,f69,f135,f279,f284,f265])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),X0,X1) != k1_tarski(sK2(sK0,X0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,sK0)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f264])).

fof(f284,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f282])).

fof(f279,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f277])).

fof(f135,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f64,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f285,plain,
    ( spl5_36
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f274,f208,f72,f282])).

fof(f72,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f208,plain,
    ( spl5_25
  <=> m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f274,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f74,f210,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f210,plain,
    ( m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f208])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f280,plain,
    ( spl5_35
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f275,f208,f82,f72,f277])).

fof(f82,plain,
    ( spl5_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f275,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0)
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f84,f74,f210,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f84,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f266,plain,
    ( spl5_20
    | spl5_33
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f255,f182,f264,f173])).

fof(f173,plain,
    ( spl5_20
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f182,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0)
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),X0,X1) != k1_tarski(sK2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | ~ v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl5_21 ),
    inference(superposition,[],[f183,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f183,plain,
    ( ! [X0,X1] :
        ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f229,plain,
    ( spl5_27
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f223,f214,f166,f219])).

fof(f166,plain,
    ( spl5_19
  <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f214,plain,
    ( spl5_26
  <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f223,plain,
    ( k1_tarski(sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))))
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f168,f216])).

fof(f216,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f168,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f217,plain,
    ( spl5_26
    | ~ spl5_14
    | spl5_20 ),
    inference(avatar_split_clause,[],[f212,f173,f133,f214])).

fof(f212,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1))
    | ~ spl5_14
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f135,f175,f48])).

fof(f175,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f211,plain,
    ( spl5_25
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f198,f161,f208])).

fof(f161,plain,
    ( spl5_18
  <=> r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f198,plain,
    ( m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f163,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f163,plain,
    ( r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f184,plain,
    ( spl5_6
    | ~ spl5_5
    | ~ spl5_3
    | spl5_21
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f180,f117,f182,f72,f82,f87])).

fof(f87,plain,
    ( spl5_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f117,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0)
        | v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0)
        | v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f118,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(f118,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f176,plain,
    ( ~ spl5_20
    | ~ spl5_2
    | spl5_16 ),
    inference(avatar_split_clause,[],[f171,f151,f67,f173])).

fof(f151,plain,
    ( spl5_16
  <=> sP4(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f171,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f69,f153,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f59_D])).

fof(f59_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f153,plain,
    ( ~ sP4(sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f169,plain,
    ( ~ spl5_14
    | spl5_19
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f147,f123,f166,f133])).

fof(f123,plain,
    ( spl5_12
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f147,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & ! [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

fof(f125,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f164,plain,
    ( spl5_18
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f143,f123,f67,f161])).

fof(f143,plain,
    ( r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f69,f125,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f154,plain,
    ( ~ spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f146,f123,f151])).

fof(f146,plain,
    ( ~ sP4(sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f125,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f51,f59_D])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f136,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f131,f87,f82,f72,f67,f62,f133])).

fof(f131,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f89,f84,f74,f64,f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f126,plain,
    ( spl5_12
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f120,f87,f82,f72,f67,f62,f123])).

fof(f120,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f89,f84,f74,f64,f69,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f115,f82,f117,f77,f72])).

fof(f77,plain,
    ( spl5_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f55,f84])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f90,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f41,f72])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f67])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f62])).

fof(f44,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (1707)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.47  % (1715)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.47  % (1705)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.47  % (1707)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f350,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f119,f126,f136,f154,f164,f169,f176,f184,f211,f217,f229,f266,f280,f285,f346])).
% 0.21/0.47  fof(f346,plain,(
% 0.21/0.47    ~spl5_27 | spl5_1 | ~spl5_2 | ~spl5_14 | ~spl5_33 | ~spl5_35 | ~spl5_36),
% 0.21/0.47    inference(avatar_split_clause,[],[f327,f282,f277,f264,f133,f67,f62,f219])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    spl5_27 <=> k1_tarski(sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl5_14 <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    spl5_33 <=> ! [X1,X0] : (k9_subset_1(u1_struct_0(sK0),X0,X1) != k1_tarski(sK2(sK0,X0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.47  fof(f277,plain,(
% 0.21/0.47    spl5_35 <=> v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    spl5_36 <=> m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    k1_tarski(sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1)))) | (spl5_1 | ~spl5_2 | ~spl5_14 | ~spl5_33 | ~spl5_35 | ~spl5_36)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f64,f69,f135,f279,f284,f265])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(sK0),X0,X1) != k1_tarski(sK2(sK0,X0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f264])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_36),
% 0.21/0.47    inference(avatar_component_clause,[],[f282])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0) | ~spl5_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f277])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl5_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    spl5_36 | ~spl5_3 | ~spl5_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f274,f208,f72,f282])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl5_3 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    spl5_25 <=> m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | ~spl5_25)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f74,f210,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f208])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    spl5_35 | ~spl5_3 | ~spl5_5 | ~spl5_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f275,f208,f82,f72,f277])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl5_5 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0) | (~spl5_3 | ~spl5_5 | ~spl5_25)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f84,f74,f210,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    spl5_20 | spl5_33 | ~spl5_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f255,f182,f264,f173])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl5_20 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl5_21 <=> ! [X1,X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(sK0),X0,X1) != k1_tarski(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | ~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl5_21),
% 0.21/0.47    inference(superposition,[],[f183,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f182])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    spl5_27 | ~spl5_19 | ~spl5_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f223,f214,f166,f219])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    spl5_19 <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    spl5_26 <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    k1_tarski(sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1)))) | (~spl5_19 | ~spl5_26)),
% 0.21/0.47    inference(backward_demodulation,[],[f168,f216])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1)) | ~spl5_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f214])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) | ~spl5_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f166])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    spl5_26 | ~spl5_14 | spl5_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f212,f173,f133,f214])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1)) | (~spl5_14 | spl5_20)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f135,f175,f48])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f173])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    spl5_25 | ~spl5_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f198,f161,f208])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    spl5_18 <=> r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_18),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f163,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl5_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f161])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    spl5_6 | ~spl5_5 | ~spl5_3 | spl5_21 | ~spl5_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f180,f117,f182,f72,f82,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl5_6 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl5_11 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0) | v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_11),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f179])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,X1)) != k9_subset_1(u1_struct_0(sK0),X1,X0) | v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_11),
% 0.21/0.47    inference(resolution,[],[f118,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | v2_tex_2(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f117])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ~spl5_20 | ~spl5_2 | spl5_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f171,f151,f67,f173])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl5_16 <=> sP4(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | spl5_16)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f69,f153,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP4(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f59_D])).
% 0.21/0.48  fof(f59_D,plain,(
% 0.21/0.48    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP4(X1)) )),
% 0.21/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ~sP4(sK1) | spl5_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f151])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ~spl5_14 | spl5_19 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f147,f123,f166,f133])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl5_12 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) | ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl5_12),
% 0.21/0.48    inference(resolution,[],[f125,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(X2,sK1) | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    (~v2_tex_2(sK1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f30,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ? [X1] : (~v2_tex_2(X1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK1),sK1) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f123])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl5_18 | ~spl5_2 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f143,f123,f67,f161])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f69,f125,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~spl5_16 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f146,f123,f151])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ~sP4(sK1) | ~spl5_12),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f125,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP4(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(general_splitting,[],[f51,f59_D])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f131,f87,f82,f72,f67,f62,f133])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f89,f84,f74,f64,f69,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl5_12 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f87,f82,f72,f67,f62,f123])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK1),sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f89,f84,f74,f64,f69,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~spl5_3 | ~spl5_4 | spl5_11 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f115,f82,f117,f77,f72])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl5_4 <=> v3_tdlat_3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f55,f84])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f87])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f82])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f77])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v3_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f72])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f67])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f62])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1707)------------------------------
% 0.21/0.48  % (1707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1707)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1707)Memory used [KB]: 10874
% 0.21/0.48  % (1707)Time elapsed: 0.065 s
% 0.21/0.48  % (1707)------------------------------
% 0.21/0.48  % (1707)------------------------------
% 0.21/0.48  % (1700)Success in time 0.12 s
%------------------------------------------------------------------------------
