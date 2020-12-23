%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 251 expanded)
%              Number of leaves         :   36 ( 114 expanded)
%              Depth                    :    8
%              Number of atoms          :  510 (1169 expanded)
%              Number of equality atoms :   54 ( 148 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f87,f92,f96,f100,f115,f120,f125,f135,f148,f165,f168,f175,f180,f313,f320,f328,f335,f339])).

fof(f339,plain,
    ( ~ spl4_5
    | spl4_22
    | ~ spl4_23
    | ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl4_5
    | spl4_22
    | ~ spl4_23
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f337,f179])).

fof(f179,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_23
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f337,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | spl4_22
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f336,f174])).

fof(f174,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_22
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f336,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_49 ),
    inference(resolution,[],[f334,f77])).

fof(f77,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_5
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl4_49
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f335,plain,
    ( spl4_49
    | ~ spl4_14
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f329,f326,f118,f333])).

fof(f118,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f326,plain,
    ( spl4_48
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_14
    | ~ spl4_48 ),
    inference(resolution,[],[f327,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_tarski(X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f326])).

fof(f328,plain,
    ( spl4_48
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f323,f318,f89,f70,f326])).

fof(f70,plain,
    ( spl4_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f89,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f318,plain,
    ( spl4_47
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f321,f91])).

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_4
    | ~ spl4_47 ),
    inference(resolution,[],[f319,f72])).

fof(f72,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f318])).

fof(f320,plain,
    ( spl4_47
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f316,f311,f65,f60,f55,f318])).

fof(f55,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f311,plain,
    ( spl4_46
  <=> ! [X1,X3,X0] :
        ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
        | ~ r1_tarski(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tex_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f315,f57])).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f314,f67])).

fof(f67,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(resolution,[],[f312,f62])).

fof(f62,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f312,plain,
    ( ! [X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tarski(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tex_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
        | v2_struct_0(X0) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f311])).

fof(f313,plain,(
    spl4_46 ),
    inference(avatar_split_clause,[],[f42,f311])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f180,plain,
    ( spl4_23
    | ~ spl4_6
    | ~ spl4_15
    | spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f169,f145,f141,f123,f80,f177])).

fof(f80,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f123,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f141,plain,
    ( spl4_18
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f145,plain,
    ( spl4_19
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f169,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_15
    | spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f153,f142])).

fof(f142,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f153,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f151,f82])).

fof(f82,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f151,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(superposition,[],[f124,f147])).

fof(f147,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f175,plain,
    ( ~ spl4_22
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f149,f145,f172])).

fof(f149,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f39,f147])).

fof(f39,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f25,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f168,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_7
    | spl4_21 ),
    inference(subsumption_resolution,[],[f166,f67])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_21 ),
    inference(resolution,[],[f164,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_7
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f164,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_21
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f165,plain,
    ( ~ spl4_21
    | spl4_1
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f160,f141,f94,f55,f162])).

fof(f94,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f160,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f159,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(resolution,[],[f143,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f148,plain,
    ( spl4_18
    | spl4_19
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f139,f133,f80,f145,f141])).

fof(f133,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f139,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(resolution,[],[f134,f82])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f53,f133])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f125,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f49,f123])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f120,plain,
    ( spl4_14
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f116,f113,f98,f118])).

fof(f98,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f113,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(k2_tarski(X0,X0),X1) )
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(resolution,[],[f114,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f100,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f50,f98])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f92,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f89])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f83,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (31744)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (31744)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f340,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f87,f92,f96,f100,f115,f120,f125,f135,f148,f165,f168,f175,f180,f313,f320,f328,f335,f339])).
% 0.21/0.43  fof(f339,plain,(
% 0.21/0.43    ~spl4_5 | spl4_22 | ~spl4_23 | ~spl4_49),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f338])).
% 0.21/0.43  fof(f338,plain,(
% 0.21/0.43    $false | (~spl4_5 | spl4_22 | ~spl4_23 | ~spl4_49)),
% 0.21/0.43    inference(subsumption_resolution,[],[f337,f179])).
% 0.21/0.43  fof(f179,plain,(
% 0.21/0.43    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f177])).
% 0.21/0.43  fof(f177,plain,(
% 0.21/0.43    spl4_23 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.43  fof(f337,plain,(
% 0.21/0.43    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | spl4_22 | ~spl4_49)),
% 0.21/0.43    inference(subsumption_resolution,[],[f336,f174])).
% 0.21/0.43  fof(f174,plain,(
% 0.21/0.43    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl4_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f172])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    spl4_22 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.43  fof(f336,plain,(
% 0.21/0.43    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | ~spl4_49)),
% 0.21/0.43    inference(resolution,[],[f334,f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    r2_hidden(sK2,sK1) | ~spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f75])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl4_5 <=> r2_hidden(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.43  fof(f334,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,sK1) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0))) | ~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_49),
% 0.21/0.43    inference(avatar_component_clause,[],[f333])).
% 0.21/0.43  fof(f333,plain,(
% 0.21/0.43    spl4_49 <=> ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0))) | ~r2_hidden(X0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.43  fof(f335,plain,(
% 0.21/0.43    spl4_49 | ~spl4_14 | ~spl4_48),
% 0.21/0.43    inference(avatar_split_clause,[],[f329,f326,f118,f333])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    spl4_14 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.43  fof(f326,plain,(
% 0.21/0.43    spl4_48 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.43  fof(f329,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0))) | ~r2_hidden(X0,sK1)) ) | (~spl4_14 | ~spl4_48)),
% 0.21/0.43    inference(resolution,[],[f327,f119])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl4_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f118])).
% 0.21/0.43  fof(f327,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | ~spl4_48),
% 0.21/0.43    inference(avatar_component_clause,[],[f326])).
% 0.21/0.43  fof(f328,plain,(
% 0.21/0.43    spl4_48 | ~spl4_4 | ~spl4_8 | ~spl4_47),
% 0.21/0.43    inference(avatar_split_clause,[],[f323,f318,f89,f70,f326])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl4_4 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl4_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f318,plain,(
% 0.21/0.43    spl4_47 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.43  fof(f323,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | (~spl4_4 | ~spl4_8 | ~spl4_47)),
% 0.21/0.43    inference(subsumption_resolution,[],[f321,f91])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f89])).
% 0.21/0.43  fof(f321,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | (~spl4_4 | ~spl4_47)),
% 0.21/0.43    inference(resolution,[],[f319,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    v2_tex_2(sK1,sK0) | ~spl4_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f70])).
% 0.21/0.43  fof(f319,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | ~spl4_47),
% 0.21/0.43    inference(avatar_component_clause,[],[f318])).
% 0.21/0.43  fof(f320,plain,(
% 0.21/0.43    spl4_47 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_46),
% 0.21/0.43    inference(avatar_split_clause,[],[f316,f311,f65,f60,f55,f318])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl4_3 <=> l1_pre_topc(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f311,plain,(
% 0.21/0.43    spl4_46 <=> ! [X1,X3,X0] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.43  fof(f316,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_46)),
% 0.21/0.43    inference(subsumption_resolution,[],[f315,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f315,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_46)),
% 0.21/0.43    inference(subsumption_resolution,[],[f314,f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f314,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_46)),
% 0.21/0.43    inference(resolution,[],[f312,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    v2_pre_topc(sK0) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f312,plain,(
% 0.21/0.43    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | v2_struct_0(X0)) ) | ~spl4_46),
% 0.21/0.43    inference(avatar_component_clause,[],[f311])).
% 0.21/0.43  fof(f313,plain,(
% 0.21/0.43    spl4_46),
% 0.21/0.43    inference(avatar_split_clause,[],[f42,f311])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(rectify,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.21/0.43  fof(f180,plain,(
% 0.21/0.43    spl4_23 | ~spl4_6 | ~spl4_15 | spl4_18 | ~spl4_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f169,f145,f141,f123,f80,f177])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl4_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    spl4_15 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.43  fof(f141,plain,(
% 0.21/0.43    spl4_18 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    spl4_19 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_6 | ~spl4_15 | spl4_18 | ~spl4_19)),
% 0.21/0.43    inference(subsumption_resolution,[],[f153,f142])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f141])).
% 0.21/0.43  fof(f153,plain,(
% 0.21/0.43    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_6 | ~spl4_15 | ~spl4_19)),
% 0.21/0.43    inference(subsumption_resolution,[],[f151,f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_15 | ~spl4_19)),
% 0.21/0.43    inference(superposition,[],[f124,f147])).
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl4_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f145])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f123])).
% 0.21/0.43  fof(f175,plain,(
% 0.21/0.43    ~spl4_22 | ~spl4_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f149,f145,f172])).
% 0.21/0.43  fof(f149,plain,(
% 0.21/0.43    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl4_19),
% 0.21/0.43    inference(backward_demodulation,[],[f39,f147])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f25,f24,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f9])).
% 0.21/0.43  fof(f9,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.21/0.43  fof(f168,plain,(
% 0.21/0.43    ~spl4_3 | ~spl4_7 | spl4_21),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    $false | (~spl4_3 | ~spl4_7 | spl4_21)),
% 0.21/0.43    inference(subsumption_resolution,[],[f166,f67])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    ~l1_pre_topc(sK0) | (~spl4_7 | spl4_21)),
% 0.21/0.43    inference(resolution,[],[f164,f86])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl4_7 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.43  fof(f164,plain,(
% 0.21/0.43    ~l1_struct_0(sK0) | spl4_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f162])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    spl4_21 <=> l1_struct_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    ~spl4_21 | spl4_1 | ~spl4_9 | ~spl4_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f160,f141,f94,f55,f162])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl4_9 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.43  fof(f160,plain,(
% 0.21/0.43    ~l1_struct_0(sK0) | (spl4_1 | ~spl4_9 | ~spl4_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f159,f57])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl4_9 | ~spl4_18)),
% 0.21/0.43    inference(resolution,[],[f143,f95])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl4_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f94])).
% 0.21/0.43  fof(f143,plain,(
% 0.21/0.43    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f141])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    spl4_18 | spl4_19 | ~spl4_6 | ~spl4_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f139,f133,f80,f145,f141])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    spl4_17 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_6 | ~spl4_17)),
% 0.21/0.43    inference(resolution,[],[f134,f82])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) ) | ~spl4_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f133])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    spl4_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f53,f133])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f48,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    spl4_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f49,f123])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    spl4_14 | ~spl4_10 | ~spl4_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f116,f113,f98,f118])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl4_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    spl4_13 <=> ! [X1,X0] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1)) ) | (~spl4_10 | ~spl4_13)),
% 0.21/0.43    inference(resolution,[],[f114,f99])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl4_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f98])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) ) | ~spl4_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f113])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    spl4_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f52,f113])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f47,f40])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f50,f98])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.43    inference(nnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl4_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f46,f94])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f89])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl4_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f41,f85])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f37,f80])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f75])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    r2_hidden(sK2,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f36,f70])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    v2_tex_2(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f65])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f60])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v2_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f55])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (31744)------------------------------
% 0.21/0.43  % (31744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (31744)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (31744)Memory used [KB]: 6396
% 0.21/0.43  % (31744)Time elapsed: 0.013 s
% 0.21/0.43  % (31744)------------------------------
% 0.21/0.43  % (31744)------------------------------
% 0.21/0.44  % (31736)Success in time 0.071 s
%------------------------------------------------------------------------------
