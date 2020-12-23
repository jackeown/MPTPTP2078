%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1877+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:49 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 351 expanded)
%              Number of leaves         :   31 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  792 (2120 expanded)
%              Number of equality atoms :  102 ( 383 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f74,f79,f90,f99,f106,f122,f127,f153,f161,f175,f189,f221,f228,f252,f273,f293,f303])).

fof(f303,plain,
    ( ~ spl5_4
    | spl5_6
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl5_4
    | spl5_6
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f301,f78])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | spl5_6
    | ~ spl5_21
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f300,f188])).

fof(f188,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl5_21
  <=> v2_tex_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f300,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | spl5_6
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f298,f73])).

fof(f73,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_6
  <=> v3_tex_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f298,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_33 ),
    inference(resolution,[],[f292,f62])).

fof(f62,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_4
  <=> v3_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl5_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f293,plain,
    ( spl5_33
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_26
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f285,f271,f226,f119,f50,f45,f291])).

fof(f45,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f50,plain,
    ( spl5_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f119,plain,
    ( spl5_13
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f226,plain,
    ( spl5_26
  <=> ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f271,plain,
    ( spl5_31
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | v2_tex_2(sK4(sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_26
    | ~ spl5_31 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_26
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f283,f121])).

fof(f121,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_26
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f282,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f281,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_1
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f280,f47])).

fof(f47,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_31 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_31 ),
    inference(resolution,[],[f272,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(sK4(X1,X0),X2)
      | ~ m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_tex_2(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v3_tex_2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK4(X0,X1) != X1
                & r1_tarski(X1,sK4(X0,X1))
                & v2_tex_2(sK4(X0,X1),X0)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) != X1
        & r1_tarski(X1,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sK4(X1,X0) = X0
      | ~ v2_tex_2(sK4(X1,X0),X2)
      | ~ m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_tex_2(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v3_tex_2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK4(X0,X1))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | X1 = X3
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f272,plain,
    ( ! [X0] :
        ( v2_tex_2(sK4(sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f273,plain,
    ( spl5_31
    | ~ spl5_1
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f264,f250,f226,f45,f271])).

fof(f250,plain,
    ( spl5_30
  <=> ! [X1,X0] :
        ( v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v2_tex_2(sK4(sK1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | v2_tex_2(sK4(sK1,X0),sK0) )
    | ~ spl5_1
    | ~ spl5_26
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f263,f227])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | v2_tex_2(sK4(sK1,X0),sK0) )
    | ~ spl5_1
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | v2_tex_2(sK4(sK1,X0),sK0) )
    | ~ spl5_1
    | ~ spl5_30 ),
    inference(resolution,[],[f251,f47])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | v3_tex_2(X0,sK1)
        | v2_tex_2(sK4(sK1,X0),X1) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f250])).

fof(f252,plain,
    ( spl5_30
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f232,f226,f219,f250])).

fof(f219,plain,
    ( spl5_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_tex_2(sK4(sK1,X1),X0)
        | v3_tex_2(X1,sK1)
        | ~ v2_tex_2(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v2_tex_2(sK4(sK1,X0),X1) )
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v2_tex_2(sK4(sK1,X0),X1)
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1) )
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f227,f220])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_tex_2(sK4(sK1,X1),X0)
        | v3_tex_2(X1,sK1)
        | ~ v2_tex_2(X1,sK1) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f219])).

fof(f228,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f130,f119,f50,f226])).

fof(f130,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f128,f52])).

fof(f128,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_13 ),
    inference(superposition,[],[f37,f121])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f221,plain,
    ( spl5_25
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f178,f159,f119,f50,f219])).

fof(f159,plain,
    ( spl5_18
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | v2_tex_2(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_tex_2(sK4(sK1,X1),X0)
        | v3_tex_2(X1,sK1)
        | ~ v2_tex_2(X1,sK1) )
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f177,f121])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_tex_2(sK4(sK1,X1),X0)
        | v3_tex_2(X1,sK1)
        | ~ v2_tex_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f176,f52])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_tex_2(sK4(sK1,X1),X0)
        | v3_tex_2(X1,sK1)
        | ~ v2_tex_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_18 ),
    inference(resolution,[],[f160,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f160,plain,
    ( ! [X2,X3] :
        ( ~ v2_tex_2(X2,sK1)
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | v2_tex_2(X2,X3) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f189,plain,
    ( spl5_21
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f181,f173,f96,f76,f186])).

fof(f96,plain,
    ( spl5_10
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f173,plain,
    ( spl5_20
  <=> ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f181,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f179,f78])).

fof(f179,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK2,sK1)
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(resolution,[],[f174,f98])).

fof(f98,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl5_20
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f171,f151,f124,f119,f50,f173])).

fof(f124,plain,
    ( spl5_14
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f151,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( ~ v2_tex_2(X0,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X1)
        | v2_tex_2(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK1) )
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f170,f52])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | v2_tex_2(X0,sK1) )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f169,f126])).

fof(f126,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f169,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | v2_tex_2(X0,sK1) )
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | v2_tex_2(X0,sK1) )
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(superposition,[],[f152,f121])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X1)
        | v2_tex_2(X0,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f161,plain,
    ( spl5_18
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f142,f124,f119,f50,f159])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | v2_tex_2(X2,X3) )
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f141,f121])).

fof(f141,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(X3)
        | v2_tex_2(X2,X3) )
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f140,f126])).

fof(f140,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(X3)
        | v2_tex_2(X2,X3) )
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f139,f121])).

fof(f139,plain,
    ( ! [X2,X3] :
        ( ~ v2_tex_2(X2,sK1)
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(X3)
        | v2_tex_2(X2,X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f43,f52])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X3,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(X3,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_tex_2(X3,X1)
      | ~ v2_tex_2(X2,X0)
      | X2 != X3
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

fof(f153,plain,
    ( spl5_16
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f138,f45,f151])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X1)
        | v2_tex_2(X0,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f43,f47])).

fof(f127,plain,
    ( spl5_14
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f116,f104,f87,f124])).

fof(f87,plain,
    ( spl5_9
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f104,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( u1_struct_0(sK0) = X0
        | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f116,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f89,f113])).

fof(f113,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(superposition,[],[f105,f89])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK0) = X0 )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f89,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f122,plain,
    ( spl5_13
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f113,f104,f87,f119])).

fof(f106,plain,
    ( spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f101,f45,f104])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(sK0) = X0
        | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f94,f47])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f99,plain,
    ( spl5_10
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f93,f76,f60,f45,f96])).

fof(f93,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f92,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f91,f78])).

fof(f91,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f35,f62])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f29,f87])).

fof(f29,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v3_tex_2(sK3,sK1)
    & v3_tex_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_tex_2(X3,X1)
                    & v3_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_tex_2(X3,X1)
                & v3_tex_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_tex_2(X3,sK1)
              & v3_tex_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_tex_2(X3,sK1)
            & v3_tex_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ v3_tex_2(X3,sK1)
          & v3_tex_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ v3_tex_2(X3,sK1)
        & v3_tex_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v3_tex_2(sK3,sK1)
      & v3_tex_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

% (5184)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v3_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v3_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).

fof(f79,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f69,f65,f55,f71])).

fof(f55,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f65,plain,
    ( spl5_5
  <=> v3_tex_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f69,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ spl5_3
    | spl5_5 ),
    inference(forward_demodulation,[],[f67,f57])).

fof(f57,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f67,plain,
    ( ~ v3_tex_2(sK3,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f68,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    ~ v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    v3_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
